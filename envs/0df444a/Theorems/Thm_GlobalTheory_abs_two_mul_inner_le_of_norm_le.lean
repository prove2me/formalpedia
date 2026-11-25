-- Prove2me | Theorems.Thm_GlobalTheory_abs_two_mul_inner_le_of_norm_le
-- name    : GlobalTheory.abs_two_mul_inner_le_of_norm_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:56:57.933667+00:00
-- url     : https://prove2.me/theorems/386aef80-5963-4004-b796-0a73a32c6b5c
-- title:
--   Global Theory: abs two mul inner le of norm le
-- statement:
--   The Global Theory construction uses the abs two mul inner le of norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/AbsTwoMulInnerLeOfNormSubEqInfDist.lean#L168-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/AbsTwoMulInnerLeOfNormSubEqInfDist.lean#L168-L174

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

theorem GlobalTheory.abs_two_mul_inner_le_of_norm_le {a y : E} (h₁ : ‖a‖ ≤ ‖a + y‖) (h₂ : ‖a‖ ≤ ‖a - y‖) :
    |2 * ⟪a, y⟫_ℝ| ≤ ‖y‖ ^ 2 := by sorry
