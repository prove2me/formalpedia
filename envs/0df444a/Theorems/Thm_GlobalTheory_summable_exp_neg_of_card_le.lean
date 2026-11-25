-- Prove2me | Theorems.Thm_GlobalTheory_summable_exp_neg_of_card_le
-- name    : GlobalTheory.summable_exp_neg_of_card_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:57:06.000107+00:00
-- url     : https://prove2.me/theorems/bebb84ca-2131-40d0-9f4b-131ec0a424b9
-- title:
--   Global Theory: summable exp neg of card le
-- statement:
--   The Global Theory construction uses the summable exp neg of card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GaussianSumOfOneSeparatedOfLe.lean#L44-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GaussianSumOfOneSeparatedOfLe.lean#L44-L51

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

theorem GlobalTheory.summable_exp_neg_of_card_le {ι : Type*} (f : ι → ℝ) {t C : ℝ} (hf : ∀ i, t ≤ f i)
    (hc : ∀ (s : Finset ι) u, t ≤ u → (∀ i ∈ s, f i ≤ u) → (s.card : ℝ) ≤ C * exp ((u - t) / 2)) :
    Summable (fun i => exp (-f i)) ∧ ∑' i, exp (-f i) ≤ 2 * C * exp (-t) := by sorry
