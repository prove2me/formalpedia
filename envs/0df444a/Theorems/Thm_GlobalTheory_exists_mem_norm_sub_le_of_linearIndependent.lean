-- Prove2me | Theorems.Thm_GlobalTheory_exists_mem_norm_sub_le_of_linearIndependent
-- name    : GlobalTheory.exists_mem_norm_sub_le_of_linearIndependent
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:57:23.671821+00:00
-- url     : https://prove2.me/theorems/6867cd09-7912-4464-b87b-c0d18193646d
-- title:
--   Global Theory: exists mem norm sub le of linear Independent
-- statement:
--   The Global Theory construction uses the exists mem norm sub le of linear Independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/AbsTwoMulInnerLeOfNormSubEqInfDist.lean#L116-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/AbsTwoMulInnerLeOfNormSubEqInfDist.lean#L116-L123

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

theorem GlobalTheory.exists_mem_norm_sub_le_of_linearIndependent [FiniteDimensional ℝ E] {ι : Type*}
    [Fintype ι] {v : ι → E} {r : ℝ} (hv : LinearIndependent ℝ v)
    (hn : Fintype.card ι = finrank ℝ E) (hL : ∀ i, v i ∈ L) (hr : ∀ i, ‖v i‖ ≤ r) (x : E) :
    ∃ w ∈ L, ‖x - w‖ ≤ √(finrank ℝ E) / 2 * r := by sorry
