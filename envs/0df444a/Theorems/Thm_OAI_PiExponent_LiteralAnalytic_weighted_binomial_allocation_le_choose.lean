-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_weighted_binomial_allocation_le_choose
-- name    : OAI.PiExponent.LiteralAnalytic.weighted_binomial_allocation_le_choose
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T17:22:43.67653+00:00
-- url     : https://prove2.me/theorems/9f634799-4471-4202-a026-9a20f9b034f1
-- title:
--   Weighted finite binomial allocation estimate
-- statement:
--   The finite sum of weighted binomial products over allocations totaling k is bounded by the product of the nonnegative weights times the stated binomial coefficient. When the total exponent is positive, the unweighted sum equals choose(k + E - 1, k). When the total exponent is zero, it is one at degree zero and zero at positive degrees.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.weighted_binomial_allocation_le_choose
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (e : σ → ℕ) (A : σ → ℝ) (k : ℕ)
    (hA : ∀ i, 0 ≤ A i) :
    ∑ n : σ → Fin (k + 1),
      (if ∑ i, (n i : ℕ) = k then
        ∏ i, (A i *
          (if e i = 0 then (if (n i : ℕ) = 0 then (1 : ℝ) else 0)
           else (Nat.choose ((n i : ℕ) + e i - 1) (n i : ℕ) : ℝ)))
       else 0) ≤
      (∏ i, A i) * (Nat.choose (k + ∑ i, e i) k : ℝ) := by
  sorry
