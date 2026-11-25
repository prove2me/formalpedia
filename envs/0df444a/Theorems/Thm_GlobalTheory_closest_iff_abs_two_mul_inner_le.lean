-- Prove2me | Theorems.Thm_GlobalTheory_closest_iff_abs_two_mul_inner_le
-- name    : GlobalTheory.closest_iff_abs_two_mul_inner_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:44:04.810446+00:00
-- url     : https://prove2.me/theorems/17e37657-3101-4ffa-9666-bc5ac1bf882b
-- title:
--   Global Theory: closest iff abs two mul inner le
-- statement:
--   The Global Theory construction uses the closest iff abs two mul inner le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/AbsTwoMulInnerLeOfNormSubEqInfDist.lean#L182-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/AbsTwoMulInnerLeOfNormSubEqInfDist.lean#L182-L188

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_AbsTwoMulInnerLeOfNormSubEqInfDist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open scoped InnerProductSpace
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {L : Submodule ℤ E}

theorem GlobalTheory.closest_iff_abs_two_mul_inner_le {p w : E} (hw : w ∈ L) :
    (∀ z ∈ L, ‖p - w‖ ≤ ‖p - z‖) ↔ ∀ y ∈ L, |2 * ⟪p - w, y⟫_ℝ| ≤ ‖y‖ ^ 2 := by sorry
