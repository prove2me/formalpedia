-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_sum_row_weights_eq_mean
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.sum_row_weights_eq_mean
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T12:38:58.150736+00:00
-- url     : https://prove2.me/theorems/7f9e81a3-de02-4c00-939d-d86720b4aa06
-- title:
--   Row-weight sum equals the actual mean normalization
-- statement:
--   Identify the sum of the rows’ weighted coordinates with the row count times height times `actualMean`. Unfold the actual mean and row-weight definitions, reorder the finite sums, and use positive height and the nonempty finite row type to justify the normalization. This removes the averaging conversion from the parent while retaining the strict positivity needed for division.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.sum_row_weights_eq_mean
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    (∑ r : Row d H,
      ∑ i : Fin d.m,
        MatrixArithmetic.logWeights (finiteDenominators d) i * (r.2.1 i.succ : ℝ)) =
      (actualRowCount d H : ℝ) * H * actualMean d H := by sorry
