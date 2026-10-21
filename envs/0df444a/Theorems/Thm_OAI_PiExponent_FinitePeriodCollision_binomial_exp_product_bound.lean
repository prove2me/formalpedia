-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_binomial_exp_product_bound
-- name    : OAI.PiExponent.FinitePeriodCollision.binomial_exp_product_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T13:41:26.177573+00:00
-- url     : https://prove2.me/theorems/7dd99737-cc67-44d2-b1a7-7aa1c5d99de1
-- title:
--   Multiplying nonnegative exponential bounds
-- statement:
--   If every factor is nonnegative and bounded by an exponential, the finite product is bounded by the exponential of the sum. Apply `Finset.prod_le_prod` to the factor bounds and use the finite-product identity for `Real.exp`. Nonnegativity is needed for product monotonicity; it holds for the cast binomial factors in the parent. This removes the product aggregation from the parent and also applies when the index type is empty.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic

open scoped BigOperators
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.binomial_exp_product_bound
    {m : ℕ} (x b : Fin m → ℝ)
    (hx : ∀ i, 0 ≤ x i) (h : ∀ i, x i ≤ Real.exp (b i)) :
    (∏ i, x i) ≤ Real.exp (∑ i, b i) := by sorry
