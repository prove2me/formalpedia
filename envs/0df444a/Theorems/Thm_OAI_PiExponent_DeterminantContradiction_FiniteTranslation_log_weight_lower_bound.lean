-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_log_weight_lower_bound
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_weight_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T17:49:31.344771+00:00
-- url     : https://prove2.me/theorems/49e484c4-5310-49ff-9ad0-8fa822eec869
-- title:
--   Fixed translation data has the stated minimum logarithmic weight
-- statement:
--   For each coordinate of `FixedData`, its minimum weight `wstar` is at most the corresponding rounded logarithm of the denominator.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_weight_lower_bound
    {nu : ℝ} (d : FixedData nu) (i : Fin d.m) :
    d.wstar ≤ MatrixArithmetic.logWeights (finiteDenominators d) i := by sorry
