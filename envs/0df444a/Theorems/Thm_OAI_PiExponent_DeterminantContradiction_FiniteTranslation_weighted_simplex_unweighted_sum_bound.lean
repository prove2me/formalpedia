-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_weighted_simplex_unweighted_sum_bound
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.weighted_simplex_unweighted_sum_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T17:49:04.712606+00:00
-- url     : https://prove2.me/theorems/492c085c-67c3-44e6-b0bf-4787ad83b08b
-- title:
--   Unweighted sum bounded by a positive minimum weight on the real weighted simplex
-- statement:
--   For a natural-number vector in the real weighted simplex, if every coordinate weight is at least a positive `wstar`, then the sum of its coordinates is at most `H / wstar`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily

open scoped BigOperators
open OAI.PiExponent

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.weighted_simplex_unweighted_sum_bound
    {m : ℕ} (w : Fin m → ℝ) (H wstar : ℝ) (hwstar : 0 < wstar)
    (hw : ∀ i : Fin m, wstar ≤ w i) (a : Fin m → ℕ)
    (ha : a ∈ realWeightedSimplex w H) :
    (∑ i : Fin m, (a i : ℝ)) ≤ H / wstar := by sorry
