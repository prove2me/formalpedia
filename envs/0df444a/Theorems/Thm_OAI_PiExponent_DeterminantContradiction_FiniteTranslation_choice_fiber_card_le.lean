-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_choice_fiber_card_le
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.choice_fiber_card_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T22:26:22.916793+00:00
-- url     : https://prove2.me/theorems/2d39cb33-25e2-47b9-822a-b5934a574b61
-- title:
--   Bound for one translation choice fiber
-- statement:
--   For a fixed row and translation index, the number of translation choices in that fiber is bounded by the product of the per-coordinate allowance and the zeroth-coordinate allowance.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.choice_fiber_card_le
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (r : Row d H) (a : Index d H) :
    (Fintype.card
      ((∀ i : Fin d.m, Fin (a.1 i - r.2.1 i.succ + 1)) ×
        Fin (r.2.1 0 + 1)) : ℝ) ≤
      (H + 1) ^ d.m * (H / (d.v0 : ℝ) + 1) := by sorry
