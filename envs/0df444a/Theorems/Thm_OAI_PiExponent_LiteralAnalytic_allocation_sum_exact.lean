-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_allocation_sum_exact
-- name    : OAI.PiExponent.LiteralAnalytic.allocation_sum_exact
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T17:55:57.237258+00:00
-- url     : https://prove2.me/theorems/e84eb5df-8d3d-4054-b8cb-27dc39090692
-- title:
--   Evaluate the binomial allocation coefficient sum exactly
-- statement:
--   The allocation sum is 1 at degree zero and 0 at positive degree when every exponent is zero. When their total E is positive, it equals the multichoose coefficient (k + E − 1).choose k.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.allocation_sum_exact
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (e : σ → ℕ) (k : ℕ) :
    (∑ n : σ → Fin (k + 1),
      (if ∑ i, (n i : ℕ) = k then
        ∏ i,
          (if e i = 0 then (if (n i : ℕ) = 0 then (1 : ℝ) else 0)
           else (Nat.choose ((n i : ℕ) + e i - 1) (n i : ℕ) : ℝ))
       else 0)) =
      (if ∑ i, e i = 0 then (if k = 0 then (1 : ℝ) else 0)
       else (Nat.choose (k + (∑ i, e i) - 1) k : ℝ)) := by sorry
