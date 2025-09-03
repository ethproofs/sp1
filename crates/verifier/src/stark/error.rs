extern crate alloc;

use alloc::string::String;
use thiserror::Error;

use sp1_stark::MachineVerificationError;

use super::{CoreSC, InnerSC};

#[derive(Debug, Error)]
pub enum StarkError {
    #[error("Invalid public values")]
    InvalidPublicValues,
    #[error("Version mismatch")]
    VersionMismatch(String),
    #[error("Core machine verification error: {0}")]
    Core(MachineVerificationError<CoreSC>),
    #[error("Recursion verification error: {0}")]
    Recursion(MachineVerificationError<InnerSC>),
}
