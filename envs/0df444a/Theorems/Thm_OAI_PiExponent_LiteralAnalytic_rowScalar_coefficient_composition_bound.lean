-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_rowScalar_coefficient_composition_bound
-- name    : OAI.PiExponent.LiteralAnalytic.rowScalar_coefficient_composition_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T12:32:53.140159+00:00
-- url     : https://prove2.me/theorems/0eceb362-528d-4305-b206-486eea246620
-- title:
--   Power-series product coefficient bound by degree allocations
-- statement:
--   For power series whose coefficients have norm at most one, the coefficient of degree k in a finite product of powers is bounded by the number of degree allocations among the individual factors, with that count bounded by 2^k times 2 raised to the total number of factors.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.RingTheory.PowerSeries.Order

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.rowScalar_coefficient_composition_bound
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (τ : σ → PowerSeries ℂ) (e : σ → ℕ) (k : ℕ)
    (hτc : ∀ i n, ‖PowerSeries.coeff n (τ i)‖ ≤ 1) :
    ‖PowerSeries.coeff k (∏ i, τ i ^ (e i : ℕ))‖ ≤
      Real.exp (Real.log 2 * (k : ℝ)) * (2 : ℝ) ^ (∑ i, e i) := by sorry
