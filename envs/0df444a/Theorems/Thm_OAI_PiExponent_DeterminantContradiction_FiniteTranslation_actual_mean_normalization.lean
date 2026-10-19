-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_actual_mean_normalization
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.actual_mean_normalization
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T12:56:28.0295+00:00
-- url     : https://prove2.me/theorems/74affad9-92c9-47ae-afdd-e666c59c91c7
-- title:
--   Mean normalization recovers the row-weight sum
-- statement:
--   At positive height, multiplying the actual mean row weight by the row count and height recovers the total row-weight sum.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.actual_mean_normalization
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    (actualRowCount d H : ℝ) * H * actualMean d H =
      MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta
        (finiteDenominators d) H := by sorry
