-- Prove2me | Theorems.Thm_GlobalTheory_exists_mem_norm_sub_le_lastMin_of_mem_span
-- name    : GlobalTheory.exists_mem_norm_sub_le_lastMin_of_mem_span
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:56:55.179121+00:00
-- url     : https://prove2.me/theorems/7293dbbb-8cb7-4ab0-a1b4-f09b51b4aaea
-- title:
--   Global Theory: exists mem norm sub le last Min of mem span
-- statement:
--   The Global Theory construction uses the exists mem norm sub le last Min of mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/AbsTwoMulInnerLeOfNormSubEqInfDist.lean#L131-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/AbsTwoMulInnerLeOfNormSubEqInfDist.lean#L131-L141

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

theorem GlobalTheory.exists_mem_norm_sub_le_lastMin_of_mem_span [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] {x : E} (hx : x ∈ span ℝ (L : Set E)) :
    ∃ w ∈ L, ‖x - w‖ ≤ √(finrank ℤ L) / 2 * lastMin L := by sorry
