-- Prove2me | Theorems.Thm_GlobalTheory_abs_two_mul_inner_le_of_closest
-- name    : GlobalTheory.abs_two_mul_inner_le_of_closest
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:57:04.47988+00:00
-- url     : https://prove2.me/theorems/94996382-f1e1-45ea-ab27-865097dc04ff
-- title:
--   Global Theory: abs two mul inner le of closest
-- statement:
--   The Global Theory construction uses the abs two mul inner le of closest property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/AbsTwoMulInnerLeOfNormSubEqInfDist.lean#L176-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/AbsTwoMulInnerLeOfNormSubEqInfDist.lean#L176-L180

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

theorem GlobalTheory.abs_two_mul_inner_le_of_closest {p w : E} (hw : w ∈ L)
    (h : ∀ z ∈ L, ‖p - w‖ ≤ ‖p - z‖) {y : E} (hy : y ∈ L) : |2 * ⟪p - w, y⟫_ℝ| ≤ ‖y‖ ^ 2 := by sorry
