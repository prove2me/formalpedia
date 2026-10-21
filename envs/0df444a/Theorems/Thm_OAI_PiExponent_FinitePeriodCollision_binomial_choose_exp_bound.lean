-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_binomial_choose_exp_bound
-- name    : OAI.PiExponent.FinitePeriodCollision.binomial_choose_exp_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T13:41:06.19819+00:00
-- url     : https://prove2.me/theorems/9f50dce1-ebeb-4368-a6e5-201121eeba52
-- title:
--   A binomial coefficient has exponential growth
-- statement:
--   Every binomial coefficient in row `n` is at most `exp (n * log 2)`, including the zero case `k > n`. The proof route is to bound an in-range term by the full sum `∑ j ∈ range (n + 1), n.choose j`, use `Nat.sum_range_choose`, and identify `2^n` with the stated exponential. This removes the single-factor estimate from the parent. The cases `n = 0` and `k > n` are covered by the same row-sum bound or the vanishing of out-of-range coefficients.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic

open scoped BigOperators
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.binomial_choose_exp_bound (n k : ℕ) :
    ((n.choose k : ℕ) : ℝ) ≤ Real.exp ((n : ℝ) * Real.log 2) := by sorry
