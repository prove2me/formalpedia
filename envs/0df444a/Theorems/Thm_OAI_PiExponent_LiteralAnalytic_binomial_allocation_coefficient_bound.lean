-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_binomial_allocation_coefficient_bound
-- name    : OAI.PiExponent.LiteralAnalytic.binomial_allocation_coefficient_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:35:47.467501+00:00
-- url     : https://prove2.me/theorems/1721c062-4ff9-40bc-a4d7-9f9106bb4f6a
-- title:
--   Bound the unweighted binomial allocation coefficient sum
-- statement:
--   For any finite exponent family and degree k, the unweighted sum of allocation coefficients is bounded by the binomial coefficient with upper argument k plus the total exponent. If all exponents vanish, only the zero allocation can contribute; for positive total exponent, the coefficient convolution is bounded by the stated binomial coefficient.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.binomial_allocation_coefficient_bound
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (e : σ → ℕ) (k : ℕ) :
    (∑ n : σ → Fin (k + 1),
      (if ∑ i, (n i : ℕ) = k then
        ∏ i,
          (if e i = 0 then (if (n i : ℕ) = 0 then (1 : ℝ) else 0)
           else (Nat.choose ((n i : ℕ) + e i - 1) (n i : ℕ) : ℝ))
       else 0)) ≤ (Nat.choose (k + ∑ i, e i) k : ℝ) := by sorry
