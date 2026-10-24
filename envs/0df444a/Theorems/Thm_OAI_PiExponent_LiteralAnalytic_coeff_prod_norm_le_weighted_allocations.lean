-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_coeff_prod_norm_le_weighted_allocations
-- name    : OAI.PiExponent.LiteralAnalytic.coeff_prod_norm_le_weighted_allocations
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:22:30.800193+00:00
-- url     : https://prove2.me/theorems/f079e64a-8aa6-4149-8ae5-0487b79619ab
-- title:
--   Weighted coefficient bound by finite degree allocations
-- statement:
--   The norm of the degree-k coefficient of the product is bounded by the sum of the products of the supplied coefficient bounds over allocations totaling k. Coordinates range from zero through k inclusively. The statement includes degree zero, zero exponents, zero weights, and the empty family.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Order

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.coeff_prod_norm_le_weighted_allocations
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (f : σ → PowerSeries ℂ) (e : σ → ℕ) (A : σ → ℝ) (k : ℕ)
    (hA : ∀ i, 0 ≤ A i)
    (hf : ∀ i n,
      ‖PowerSeries.coeff n (f i)‖ ≤
        A i *
          (if e i = 0 then (if n = 0 then (1 : ℝ) else 0)
           else (Nat.choose (n + e i - 1) n : ℝ))) :
    ‖PowerSeries.coeff k (∏ i, f i)‖ ≤
      ∑ n : σ → Fin (k + 1),
        (if ∑ i, (n i : ℕ) = k then
          ∏ i, (A i *
            (if e i = 0 then (if (n i : ℕ) = 0 then (1 : ℝ) else 0)
             else (Nat.choose ((n i : ℕ) + e i - 1) (n i : ℕ) : ℝ)))
         else 0) := by
  sorry
