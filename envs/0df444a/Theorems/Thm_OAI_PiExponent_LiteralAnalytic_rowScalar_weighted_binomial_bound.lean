-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_rowScalar_weighted_binomial_bound
-- name    : OAI.PiExponent.LiteralAnalytic.rowScalar_weighted_binomial_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T12:33:05.717175+00:00
-- url     : https://prove2.me/theorems/0d0e58f8-0d6e-4921-8614-1a72714b7a5b
-- title:
--   Weighted binomial product bound
-- statement:
--   The product of the two binomial factors at each index, weighted by 2 to the sum of the selected exponents, is bounded by 4 to the sum of the ambient parameters. The Fin-range condition on each exponent ensures it does not exceed the truncated difference a i − β i.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.rowScalar_weighted_binomial_bound
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (a β : σ →₀ ℕ) (e : ∀ i, Fin (a i - β i + 1)) :
    ((∏ i, (a i).choose (β i) * (a i - β i).choose (e i) : ℕ) : ℝ) *
      (2 : ℝ) ^ (∑ i, (e i : ℕ)) ≤
        Real.exp (Real.log 4 * (∑ i, (a i : ℝ))) := by sorry
