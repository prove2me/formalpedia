-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_coefficient_product_pow_le_choose_weighted
-- name    : OAI.PiExponent.LiteralAnalytic.coefficient_product_pow_le_choose_weighted
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T16:33:38.814858+00:00
-- url     : https://prove2.me/theorems/49aaba7d-6d95-4242-880c-760cd8d5eb01
-- title:
--   Weighted coefficient bound for products of powers of power series
-- statement:
--   If every coefficient of each series τ i has norm at most C i, then the degree-k coefficient of their finite product of powers is bounded by the product of the coefficient bounds, raised to their respective exponents, times the binomial allocation bound.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Order

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.coefficient_product_pow_le_choose_weighted
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (τ : σ → PowerSeries ℂ) (e : σ → ℕ) (k : ℕ) (C : σ → ℝ)
    (hτc : ∀ i n, ‖PowerSeries.coeff n (τ i)‖ ≤ C i) :
    ‖PowerSeries.coeff k (∏ i, τ i ^ (e i : ℕ))‖ ≤
      (∏ i, C i ^ e i) * (Nat.choose (k + ∑ i, e i) k : ℝ) := by sorry
