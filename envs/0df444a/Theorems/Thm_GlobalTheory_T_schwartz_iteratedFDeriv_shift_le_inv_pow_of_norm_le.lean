-- Prove2me | Theorems.Thm_GlobalTheory_T_schwartz_iteratedFDeriv_shift_le_inv_pow_of_norm_le
-- name    : GlobalTheory.T.schwartz_iteratedFDeriv_shift_le_inv_pow_of_norm_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:37:01.808126+00:00
-- url     : https://prove2.me/theorems/d4dcc681-afb2-551e-80e6-135ca9ec1e85
-- title:
--   T: schwartz iterated FDeriv shift le inv pow of norm le
-- statement:
--   The T construction uses the schwartz iterated FDeriv shift le inv pow of norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzShiftIteratedFDerivBoundStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzShiftIteratedFDerivBoundStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzShiftIteratedFDerivBound
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzShiftIteratedFDerivBoundStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.schwartz_iteratedFDeriv_shift_le_inv_pow_of_norm_le : ∀ {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (f : SchwartzMap V ℂ) (a : V) (p : E →L[ℝ] V) (n M : ℕ) (R : ℝ), ∃ C : ℝ, ∀ y t, ‖t‖ ≤ R → ‖iteratedFDeriv ℝ n (fun t => f (y + a + p t)) t‖ ≤ C * ((1 + ‖y‖) ^ M)⁻¹ := by sorry
