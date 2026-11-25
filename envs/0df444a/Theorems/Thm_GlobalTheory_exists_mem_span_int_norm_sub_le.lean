-- Prove2me | Theorems.Thm_GlobalTheory_exists_mem_span_int_norm_sub_le
-- name    : GlobalTheory.exists_mem_span_int_norm_sub_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:56:56.612928+00:00
-- url     : https://prove2.me/theorems/d894a8f3-da39-4376-b816-d17db4b91080
-- title:
--   Global Theory: exists mem span int norm sub le
-- statement:
--   The Global Theory construction uses the exists mem span int norm sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/AbsTwoMulInnerLeOfNormSubEqInfDist.lean#L68-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/AbsTwoMulInnerLeOfNormSubEqInfDist.lean#L68-L84

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

theorem GlobalTheory.exists_mem_span_int_norm_sub_le {ι : Type*} [Fintype ι] (v : ι → E) {r : ℝ}
    (hr : ∀ i, ‖v i‖ ≤ r) {x : E} (hx : x ∈ span ℝ (Set.range v)) :
    ∃ w ∈ span ℤ (Set.range v), ‖x - w‖ ≤ √(Fintype.card ι) / 2 * r := by sorry
