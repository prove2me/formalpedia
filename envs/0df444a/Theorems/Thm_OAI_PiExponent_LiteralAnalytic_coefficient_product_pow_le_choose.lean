-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_coefficient_product_pow_le_choose
-- name    : OAI.PiExponent.LiteralAnalytic.coefficient_product_pow_le_choose
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T12:55:25.87519+00:00
-- url     : https://prove2.me/theorems/b7fe7024-ad63-43c7-9081-1997c583c08a
-- title:
--   Bound a product coefficient by a degree-allocation count
-- statement:
--   The coefficient of degree k in a finite product of powers of series with coefficients bounded by one is bounded by a binomial count of possible degree allocations. This also covers the empty product and zero-degree cases.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Order

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.coefficient_product_pow_le_choose
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (τ : σ → PowerSeries ℂ) (e : σ → ℕ) (k : ℕ)
    (hτc : ∀ i n, ‖PowerSeries.coeff n (τ i)‖ ≤ 1) :
    ‖PowerSeries.coeff k (∏ i, τ i ^ (e i : ℕ))‖ ≤
      (Nat.choose (k + ∑ i, e i) k : ℝ) := by sorry
