-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_choice_card_le_index_mul_fiber_bound
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.choice_card_le_index_mul_fiber_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T22:26:37.510337+00:00
-- url     : https://prove2.me/theorems/391d0523-e43e-43bf-8d9c-208fb46a27f1
-- title:
--   Sigma cardinality from a uniform fiber bound
-- statement:
--   The total number of choices for a row is at most the number of indices times the uniform bound for one choice fiber.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.choice_card_le_index_mul_fiber_bound
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (r : Row d H) :
    (Fintype.card (Choice d H r) : ℝ) ≤
      (Fintype.card (Index d H) : ℝ) *
        ((H + 1) ^ d.m * (H / (d.v0 : ℝ) + 1)) := by sorry
