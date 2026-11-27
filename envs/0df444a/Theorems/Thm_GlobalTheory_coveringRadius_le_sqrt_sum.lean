-- Prove2me | Theorems.Thm_GlobalTheory_coveringRadius_le_sqrt_sum
-- name    : GlobalTheory.coveringRadius_le_sqrt_sum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:43:47.462179+00:00
-- url     : https://prove2.me/theorems/8ef535cc-b42a-5a9b-a03c-eaf3c172d567
-- title:
--   Global Theory: covering Radius le sqrt sum
-- statement:
--   The Global Theory construction uses the covering Radius le sqrt sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/AbsTwoMulInnerLeOfNormSubEqInfDist.lean#L100-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/AbsTwoMulInnerLeOfNormSubEqInfDist.lean#L100-L107

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

theorem GlobalTheory.coveringRadius_le_sqrt_sum {ι : Type*} [Fintype ι] {v : ι → E}
    (hv : span ℝ (Set.range v) = ⊤) (hL : ∀ i, v i ∈ L) :
    coveringRadius L ≤ √(∑ i, ‖v i‖ ^ 2) / 2 := by sorry
