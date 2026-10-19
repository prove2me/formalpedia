-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_scalar_product_bound
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.scalar_product_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T12:24:47.750382+00:00
-- url     : https://prove2.me/theorems/a513ea30-1736-4a9b-9be1-0c8d2ff886e2
-- title:
--   Approximation and tail bound for translation scalar products
-- statement:
--   For nonnegative nu and positive height, the product of translation scalars decays with the total excess index weight, up to the specified translation error.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.scalar_product_bound
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ} (hH : 0 < H)
    (f : Family d H) :
    ‖∏ r : Row d H, scalar d r (f r)‖ ≤
      Real.exp (-nu * ((∑ r : Row d H, weight d (f r).1) -
        (actualRowCount d H : ℝ) * H * actualMean d H) +
        (actualRowCount d H : ℝ) * H * d.translationError) := by sorry
