-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_small_weight_indices_image_subset_low_simplex
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.small_weight_indices_image_subset_low_simplex
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T13:00:18.190976+00:00
-- url     : https://prove2.me/theorems/2b76aa41-354a-4a1f-a04b-55bac276ee22
-- title:
--   Selected index vectors lie in the low simplex
-- statement:
--   Every selected exponent vector, viewed in its underlying function type, belongs to the weighted simplex of height A·H.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.small_weight_indices_image_subset_low_simplex
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    (Finset.univ.filter
      (fun a : Index d H => weight d a ≤ (d.base.A : ℝ) * H)).image
        (fun a => a.1) ⊆
      realWeightedSimplex (MatrixArithmetic.logWeights (finiteDenominators d))
        ((d.base.A : ℝ) * H) := by sorry
