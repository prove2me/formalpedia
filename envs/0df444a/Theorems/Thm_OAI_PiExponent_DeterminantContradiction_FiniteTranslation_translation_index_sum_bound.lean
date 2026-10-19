-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_translation_index_sum_bound
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_index_sum_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T17:43:56.243893+00:00
-- url     : https://prove2.me/theorems/6cb3b5ac-d4fe-40d4-8ae3-77b9c88c3acf
-- title:
--   Translation index sum from the weighted simplex bound
-- statement:
--   The sum of the translation indices is at most H divided by the positive minimum weight. The index belongs to the real weighted simplex with coordinate weights given by the rounded logarithms, and each such weight is at least `d.wstar`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_index_sum_bound
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r) :
    (∑ i : Fin d.m, (t.1.1 i : ℝ)) ≤ H / d.wstar := by sorry
