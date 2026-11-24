-- Prove2me | Theorems.Thm_GlobalTheory_finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace
-- name    : GlobalTheory.finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:49:37.629813+00:00
-- url     : https://prove2.me/theorems/8b216433-93fb-4204-807f-161a9957980b
-- title:
--   Global Theory: finrank ker aeval eq nat Degree mul finrank eigenspace
-- statement:
--   The Global Theory construction uses the finrank ker aeval eq nat Degree mul finrank eigenspace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAl.lean#L107-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAl.lean#L107-L147

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace :
    ∀ (F : Type) [Field F] [Finite F] (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι F) (f : F[X]) (y : AlgebraicClosure F), Irreducible f → aeval y f = 0 → Module.finrank F (LinearMap.ker (aeval (Matrix.toLin' M) f)) = f.natDegree * Module.finrank (AlgebraicClosure F) (Module.End.eigenspace (Matrix.toLin' (M.map (algebraMap F (AlgebraicClosure F)))) y) := by sorry
