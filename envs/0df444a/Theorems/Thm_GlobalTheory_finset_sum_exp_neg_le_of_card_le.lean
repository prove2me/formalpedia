-- Prove2me | Theorems.Thm_GlobalTheory_finset_sum_exp_neg_le_of_card_le
-- name    : GlobalTheory.finset_sum_exp_neg_le_of_card_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:56:42.777748+00:00
-- url     : https://prove2.me/theorems/9733b29e-8b45-4971-ac40-f2d80bb55d78
-- title:
--   Global Theory: finset sum exp neg le of card le
-- statement:
--   The Global Theory construction uses the finset sum exp neg le of card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GaussianSumOfOneSeparatedOfLe.lean#L8-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GaussianSumOfOneSeparatedOfLe.lean#L8-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteInterClosedBallOfSeparated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GaussianSumOfOneSeparatedOfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric MeasureTheory Module Set Real
open GlobalTheory

theorem GlobalTheory.finset_sum_exp_neg_le_of_card_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) {t C : ℝ}
    (hf : ∀ i ∈ s, t ≤ f i)
    (hc : ∀ u, t ≤ u → ((s.filter fun i => f i ≤ u).card : ℝ) ≤ C * exp ((u - t) / 2)) :
    ∑ i ∈ s, exp (-f i) ≤ 2 * C * exp (-t) := by sorry
