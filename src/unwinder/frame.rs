use gimli::{
    BaseAddresses, CfaRule, Register, RegisterRule, UnwindContext, UnwindExpression, UnwindTableRow,
};
#[cfg(feature = "dwarf-expr")]
use gimli::{Evaluation, EvaluationResult, Location, Value};

use log::trace;

use super::arch::*;
use super::find_fde::{self, FDEFinder, FDESearchResult};
use crate::abi::PersonalityRoutine;
use crate::arch::*;
use crate::util::*;

struct StoreOnStack;

// gimli's MSRV doesn't allow const generics, so we need to pick a supported array size.
const fn next_value(x: usize) -> usize {
    let supported = [0, 1, 2, 3, 4, 8, 16, 32, 64, 128];
    let mut i = 0;
    while i < supported.len() {
        if supported[i] >= x {
            return supported[i];
        }
        i += 1;
    }
    192
}

impl<O: gimli::ReaderOffset> gimli::UnwindContextStorage<O> for StoreOnStack {
    type Rules = [(Register, RegisterRule<O>); next_value(MAX_REG_RULES)];
    type Stack = [UnwindTableRow<O, Self>; 2];
}

#[cfg(feature = "dwarf-expr")]
impl<R: gimli::Reader> gimli::EvaluationStorage<R> for StoreOnStack {
    type Stack = [Value; 64];
    type ExpressionStack = [(R, R); 0];
    type Result = [gimli::Piece<R>; 1];
}

#[derive(Debug)]
struct FdeFrame {
    fde_result: FDESearchResult,
    row: UnwindTableRow<usize, StoreOnStack>,
}

#[derive(Debug)]
pub enum Frame {
    Fde(FdeFrame),
    BasePointer(usize),
}

impl Frame {
    pub fn from_context(ctx: &Context, signal: bool) -> Result<Option<Self>, gimli::Error> {
        let mut ra = ctx[Arch::RA];

        trace!("return address {ra:#x}");

        // Reached end of stack
        if ra == 0 {
            trace!("end of stack");
            return Ok(None);
        }

        // RA points to the *next* instruction, so move it back 1 byte for the call instruction.
        if !signal {
            ra -= 1;
        }

        let fde_result = match find_fde::get_finder().find_fde(ra as _) {
            Some(v) => v,
            None => {
                trace!("no fde found - trying base pointer val {:#x}", ctx[Register(6)]); // fixme: non x86_64
                return Ok(Some(Self::BasePointer(ctx[Register(6)])));
            },
        };
        let mut unwinder = UnwindContext::<_, StoreOnStack>::new_in();
        let row = fde_result
            .fde
            .unwind_info_for_address(
                &fde_result.eh_frame,
                &fde_result.bases,
                &mut unwinder,
                ra as _,
            )?
            .clone();

        Ok(Some(Self::Fde(FdeFrame { fde_result, row })))
    }
}

impl FdeFrame {
    #[cfg(feature = "dwarf-expr")]
    #[cfg_attr(kasan, no_sanitize(address))]
	#[cfg_attr(kasan, inline(never))]
    fn evaluate_expression(
        &self,
        ctx: &Context,
        expr: UnwindExpression<usize>,
    ) -> Result<usize, gimli::Error> {
        let expr = expr.get(&self.fde_result.eh_frame).unwrap();
        let mut eval =
            Evaluation::<_, StoreOnStack>::new_in(expr.0, self.fde_result.fde.cie().encoding());
        let mut result = eval.evaluate()?;
        loop {
            match result {
                EvaluationResult::Complete => break,
                EvaluationResult::RequiresMemory { address, .. } => {
                    let value = unsafe { (address as usize as *const usize).read_unaligned() };
                    result = eval.resume_with_memory(Value::Generic(value as _))?;
                }
                EvaluationResult::RequiresRegister { register, .. } => {
                    let value = ctx[register];
                    result = eval.resume_with_register(Value::Generic(value as _))?;
                }
                EvaluationResult::RequiresRelocatedAddress(address) => {
                    let value = unsafe { (address as usize as *const usize).read_unaligned() };
                    result = eval.resume_with_memory(Value::Generic(value as _))?;
                }
                _ => unreachable!(),
            }
        }

        Ok(
            match eval
                .as_result()
                .last()
                .ok_or(gimli::Error::PopWithEmptyStack)?
                .location
            {
                Location::Address { address } => address as usize,
                _ => unreachable!(),
            },
        )
    }

    #[cfg(not(feature = "dwarf-expr"))]
    fn evaluate_expression(
        &self,
        _ctx: &Context,
        _expr: UnwindExpression<usize>,
    ) -> Result<usize, gimli::Error> {
        Err(gimli::Error::UnsupportedEvaluation)
    }
}

impl Frame {
    pub fn adjust_stack_for_args(&self, ctx: &mut Context) {
        match self {
            Self::Fde(frame) => {
                let size = frame.row.saved_args_size();
                ctx[Arch::SP] = ctx[Arch::SP].wrapping_add(size as usize);
            },
            _ => todo!(),
        }
    }

    #[cfg_attr(kasan, sanitize(address = "off"))]
	#[cfg_attr(kasan, inline(never))]
    pub fn unwind(&self, ctx: &Context) -> Result<Context, gimli::Error> {
        match self {
            Self::Fde(frame) => {
                let row = &frame.row;
                let mut new_ctx = ctx.clone();

                let cfa = match *row.cfa() {
                    CfaRule::RegisterAndOffset { register, offset } => {
                        ctx[register].wrapping_add(offset as usize)
                    }
                    CfaRule::Expression(expr) => frame.evaluate_expression(ctx, expr)?,
                };

                new_ctx[Arch::SP] = cfa as _;
                new_ctx[Arch::RA] = 0;

                #[warn(non_exhaustive_omitted_patterns)]
                for (reg, rule) in row.registers() {
                    trace!("{reg:?} = {rule:?}");
                    let value = match *rule {
                        RegisterRule::Undefined | RegisterRule::SameValue => ctx[*reg],
                        RegisterRule::Offset(offset) => unsafe {
                            *((cfa.wrapping_add(offset as usize)) as *const usize)
                        },
                        RegisterRule::ValOffset(offset) => cfa.wrapping_add(offset as usize),
                        RegisterRule::Register(r) => ctx[r],
                        RegisterRule::Expression(expr) => {
                            let addr = frame.evaluate_expression(ctx, expr)?;
                            unsafe { *(addr as *const usize) }
                        }
                        RegisterRule::ValExpression(expr) => frame.evaluate_expression(ctx, expr)?,
                        RegisterRule::Architectural => unreachable!(),
                        RegisterRule::Constant(value) => value as usize,
                        _ => unreachable!(),
                    };
                    new_ctx[*reg] = value;
                }

                Ok(new_ctx)
            },
            Self::BasePointer(base_pointer) => {
                let mut new_ctx = ctx.clone();
                new_ctx[Arch::SP] = *base_pointer;

                if *base_pointer != 0 && is_canonical_addr(*base_pointer) {
                    new_ctx[Register(6)] = unsafe { *(*base_pointer as *const usize) };
                    new_ctx[Arch::RA] = unsafe { *(*base_pointer as *const usize).offset(1) };
                } else {
                    new_ctx[Arch::RA] = 0;
                }
                
                trace!("rsp = {:#x}", new_ctx[Arch::SP]);
                trace!("rbp = {:#x}", new_ctx[Register(6)]);
                trace!("rip = {:#x}", new_ctx[Arch::RA]);
                Ok(new_ctx)
            }
        }
    }

    pub fn bases(&self) -> &BaseAddresses {
        match self {
            Self::Fde(frame) => &frame.fde_result.bases,
            _ => todo!(),
        }
    }

    pub fn personality(&self) -> Option<PersonalityRoutine> {
        match self {
            Self::Fde(frame) => {
                frame.fde_result
                     .fde
                     .personality()
                     .map(|x| unsafe { deref_pointer(x) })
                     .map(|x| unsafe { core::mem::transmute(x) })
            },
            _ => todo!(),
        }
    }

    pub fn lsda(&self) -> usize {
        match self {
            Self::Fde(frame) => {
                frame.fde_result
                     .fde
                     .lsda()
                     .map(|x| unsafe { deref_pointer(x) })
                     .unwrap_or(0)
            }
            _ => todo!(),
        }
    }

    pub fn initial_address(&self) -> usize {
        match self {
            Self::Fde(frame) => frame.fde_result.fde.initial_address() as _,
            _ => todo!(),
        }
    }

    pub fn is_signal_trampoline(&self) -> bool {
        match self {
            Self::Fde(frame) => frame.fde_result.fde.is_signal_trampoline(),
            Self::BasePointer(_) => false,
        }
    }
}

fn is_canonical_addr(addr: usize) -> bool {
    #[cfg(target_arch = "x86_64")]
    {
        let mask = addr & 0xffff_8000_0000_0000;
        mask == 0 || mask == 0xffff_8000_0000_0000
    }
    #[cfg(not(target_arch = "x86_64"))] { true }
}
