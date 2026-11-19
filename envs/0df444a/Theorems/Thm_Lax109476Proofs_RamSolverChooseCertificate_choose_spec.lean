-- Prove2me | Theorems.Thm_Lax109476Proofs_RamSolverChooseCertificate_choose_spec
-- name    : Lax109476Proofs.RamSolverChooseCertificate.choose_spec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T09:16:54.398579+00:00
-- url     : https://prove2.me/theorems/ea13b72d-767b-4685-98b8-aa1cbad8da1e
-- title:
--   Bounded native selection of a linear-programming certificate
-- statement:
--   Let $P$ be an integer linear program with $m+n\le L$ and coefficient magnitudes bounded by the prescribed power of two. Suppose the saved input, certificate workspace and reconstruction stack satisfy their initialization predicates, with word width and stack depth at least the stated uniform bounds. The fixed certificate-selection command terminates within
--   $$\operatorname{instructionBound}(\operatorname{parameter}(L))$$
--   bounded operational steps and returns a valid rational certificate for $P$. The alternatives cover an optimum, infeasibility and unboundedness.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamSolverChooseCertificate.lean, theorem choose_spec

import Definitions.Def_EdgeSublinearMWIS_Main_NativeSchemeInterfaces

theorem Lax109476Proofs.RamSolverChooseCertificate.choose_spec : ∀ (m n L N w : ℕ) (P : Lax109476.LinearProgram.Program ℤ m n),
  m + n ≤ L →
    Lax109476Proofs.RamSolverBranchBounds.wordWidth (Lax109476Proofs.RamCertificateSetup.parameter L) ≤ w →
      Lax109476Proofs.RamRationalReconstruction.depthBound
              (Lax109476Proofs.RamRecoverFeasibleSystem.recoveryBits
                (Lax109476Proofs.RamCertificateSetup.parameter L)) +
            1 ≤
          N →
        (∀ (i : Fin m) (j : Fin n), (P.A i j).natAbs ≤ 2 ^ (2 * Lax109476Proofs.RamCertificateSetup.parameter L)) →
          (∀ (i : Fin m), (P.b i).natAbs ≤ 2 ^ (2 * Lax109476Proofs.RamCertificateSetup.parameter L)) →
            (∀ (j : Fin n), (P.c j).natAbs ≤ 2 ^ (2 * Lax109476Proofs.RamCertificateSetup.parameter L)) →
              Lax808846Proofs.Reasoning.Spec (2 ^ w)
                (fun (σ : Lax808846Proofs.Imp.Env) =>
                  Lax109476Proofs.RamCertificateSource.Data P σ ∧ Lax109476Proofs.RamSolverBranchSpecs.State P L N σ)
                Lax109476Proofs.RamExactSolverProgram.chooseCertificate
                (Lax109476Proofs.RamSolverBranchComposition.Result P)
                (Lax109476Proofs.RamSolverBranchBounds.instructionBound
                  (Lax109476Proofs.RamCertificateSetup.parameter L)) := by sorry
