-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_selected_weight_dominates_row_sum
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.selected_weight_dominates_row_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T12:56:14.492975+00:00
-- url     : https://prove2.me/theorems/5c287ccb-2663-4c5b-a59e-5e11a8a6e593
-- title:
--   Chosen index weight dominates total row weight
-- statement:
--   For any family of row choices, the sum of row tail weights is bounded by the sum of the chosen index weights. The product nonzero premise is retained to match the parent interface.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.selected_weight_dominates_row_sum
    {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (f : Family d H)
    (hf : (∏ r : Row d H, scalar d r (f r)) ≠ 0) :
    MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta
        (finiteDenominators d) H ≤
      ∑ r : Row d H, weight d (f r).1 := by sorry
