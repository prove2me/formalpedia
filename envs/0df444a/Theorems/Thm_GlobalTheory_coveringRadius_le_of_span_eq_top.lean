-- Prove2me | Theorems.Thm_GlobalTheory_coveringRadius_le_of_span_eq_top
-- name    : GlobalTheory.coveringRadius_le_of_span_eq_top
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:44:31.939207+00:00
-- url     : https://prove2.me/theorems/da9db3b8-de24-5c21-8636-e40fbee0dbaf
-- title:
--   Global Theory: covering Radius le of span eq top
-- statement:
--   The Global Theory construction uses the covering Radius le of span eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/AbsTwoMulInnerLeOfNormSubEqInfDist.lean#L109-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/AbsTwoMulInnerLeOfNormSubEqInfDist.lean#L109-L114

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

theorem GlobalTheory.coveringRadius_le_of_span_eq_top {ι : Type*} [Fintype ι] {v : ι → E} {r : ℝ}
    (hv : span ℝ (Set.range v) = ⊤) (hL : ∀ i, v i ∈ L) (hr : ∀ i, ‖v i‖ ≤ r) :
    coveringRadius L ≤ √(Fintype.card ι) / 2 * r := by sorry
