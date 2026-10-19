-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_row_weight_le_selected_index_weight
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.row_weight_le_selected_index_weight
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T13:00:34.298431+00:00
-- url     : https://prove2.me/theorems/258b2bf8-e926-4c75-b917-4b0de2b881e2
-- title:
--   A selected index dominates its row's tail weight
-- statement:
--   For a fixed row, nonvanishing of the product of all selected scalars forces the row's tail exponent in each coordinate to be no larger than the corresponding selected index exponent. Since the logarithmic weights are nonnegative, the row's weighted tail sum is bounded by the selected index weight.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.row_weight_le_selected_index_weight
    {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (f : Family d H)
    (hf : (∏ r : Row d H, scalar d r (f r)) ≠ 0)
    (r : Row d H) :
    ∑ i : Fin d.m,
        (r.2.1 i.succ : ℝ) * MatrixArithmetic.logWeights (finiteDenominators d) i ≤
      weight d (f r).1 := by sorry
