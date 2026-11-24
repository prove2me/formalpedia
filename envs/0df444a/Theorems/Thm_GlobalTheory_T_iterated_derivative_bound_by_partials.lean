-- Prove2me | Theorems.Thm_GlobalTheory_T_iterated_derivative_bound_by_partials
-- name    : GlobalTheory.T.iterated_derivative_bound_by_partials
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:51:12.224476+00:00
-- url     : https://prove2.me/theorems/24bbd91a-d8be-4f94-ac9f-0ed7c9535668
-- title:
--   T: iterated derivative bound by partials
-- statement:
--   The T construction uses the iterated derivative bound by partials property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IteratedDerivativeBoundByPartialsStatement.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IteratedDerivativeBoundByPartialsStatement.lean#L10-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivativeBoundByPartials
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivativeBoundByPartialsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.iterated_derivative_bound_by_partials : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X],
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : X → ℂ), ContDiff ℝ ∞ g → ∀ (n : ℕ) (z : X),
      ‖iteratedFDeriv ℝ (n + 1) g z‖ ≤ C * ∑ i, ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ g w (Module.finBasis ℝ X i)) z‖ := by sorry
