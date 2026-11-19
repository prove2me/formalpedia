-- Prove2me | Theorems.Thm_Lax109476Proofs_RamSolverFinish_finish_spec
-- name    : Lax109476Proofs.RamSolverFinish.finish_spec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T09:17:26.407571+00:00
-- url     : https://prove2.me/theorems/268894f1-dbac-4523-ab44-7db5a9b47887
-- title:
--   Native linear-programming completion and certificate output
-- statement:
--   For a rational linear program $P$, assume the decoded input and reconstruction workspace satisfy the completion precondition, at the prescribed word width and stack depth. The fixed completion command returns a valid certificate and appends its encoding to the previous output within
--   $$\operatorname{instructionBound}(\operatorname{bitSize}(\operatorname{encode}(P))).$$
--   Signed rational coefficients are handled through exact denominator clearing.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamSolverFinish.lean, theorem finish_spec

import Definitions.Def_EdgeSublinearMWIS_Main_NativeSchemeInterfaces

theorem Lax109476Proofs.RamSolverFinish.finish_spec : ∀ (m n N w : ℕ) (P : Lax109476.LinearProgram.Program ℚ m n),
  Lax109476Proofs.RamSolverBranchBounds.wordWidth
        (Lax109476Proofs.RamCertificateSetup.parameter
          (Lax759944.BinaryWordEncoding.bitSize (Lax109476.RationalEncoding.encodeProgram P))) ≤
      w →
    Lax109476Proofs.RamRationalReconstruction.depthBound
            (Lax109476Proofs.RamRecoverFeasibleSystem.recoveryBits
              (Lax109476Proofs.RamCertificateSetup.parameter
                (Lax759944.BinaryWordEncoding.bitSize (Lax109476.RationalEncoding.encodeProgram P)))) +
          1 ≤
        N →
      Lax808846Proofs.Reasoning.Spec (2 ^ w) (Lax109476Proofs.RamSolverFinish.Input P N)
        (Lax109476Proofs.RamCertificateSetup.save.seq Lax109476Proofs.RamExactSolverProgram.chooseCertificate)
        (Lax109476Proofs.RamSolverFinish.Result P)
        (Lax109476Proofs.RamSolverFinish.instructionBound
          (Lax759944.BinaryWordEncoding.bitSize (Lax109476.RationalEncoding.encodeProgram P))) := by sorry
