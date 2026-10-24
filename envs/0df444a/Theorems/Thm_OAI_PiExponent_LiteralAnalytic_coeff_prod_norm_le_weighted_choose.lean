-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_coeff_prod_norm_le_weighted_choose
-- name    : OAI.PiExponent.LiteralAnalytic.coeff_prod_norm_le_weighted_choose
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T16:38:42.629647+00:00
-- url     : https://prove2.me/theorems/5bd5836d-6417-4d06-afc1-8774148030a9
-- title:
--   Weighted coefficient bound for finite products
-- statement:
--   For a finite family of power series whose coefficients satisfy the stated exponent-weighted bounds, the degree-k coefficient of their product is bounded by the product of the weights times the binomial allocation bound for the total exponent.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Order

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.coeff_prod_norm_le_weighted_choose
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (f : σ → PowerSeries ℂ) (e : σ → ℕ) (A : σ → ℝ) (k : ℕ)
    (hA : ∀ i, 0 ≤ A i)
    (hf : ∀ i n,
      ‖PowerSeries.coeff n (f i)‖ ≤
        A i *
          (if e i = 0 then (if n = 0 then (1 : ℝ) else 0)
           else (Nat.choose (n + e i - 1) n : ℝ))) :
    ‖PowerSeries.coeff k (∏ i, f i)‖ ≤
      (∏ i, A i) * (Nat.choose (k + ∑ i, e i) k : ℝ) := by
  sorry
