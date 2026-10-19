-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_realWeightedSimplex_mem_of_pos_weighted_sum_le
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.realWeightedSimplex_mem_of_pos_weighted_sum_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T13:11:38.319921+00:00
-- url     : https://prove2.me/theorems/0edf71a8-bcb4-4e57-8090-97606033216a
-- title:
--   Positive weighted sum bounds imply weighted simplex membership
-- statement:
--   For positive real weights and positive height, any natural-number vector whose weighted sum is at most that height belongs to the corresponding real weighted simplex.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily

open scoped BigOperators
open OAI.PiExponent

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.realWeightedSimplex_mem_of_pos_weighted_sum_le
    {m : ℕ} (w : Fin m → ℝ) {T : ℝ} (a : Fin m → ℕ)
    (hT : 0 < T) (hw : ∀ i, 0 < w i)
    (ha : ∑ i, w i * (a i : ℝ) ≤ T) :
    a ∈ realWeightedSimplex w T := by sorry
