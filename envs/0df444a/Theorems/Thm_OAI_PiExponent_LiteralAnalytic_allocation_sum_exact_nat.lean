-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_allocation_sum_exact_nat
-- name    : OAI.PiExponent.LiteralAnalytic.allocation_sum_exact_nat
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T18:01:07.662018+00:00
-- url     : https://prove2.me/theorems/41467ee5-82da-4d1f-a199-83bdf55337d1
-- title:
--   Evaluate the natural-valued binomial allocation coefficient sum
-- statement:
--   For a finite family of natural exponents, the natural-valued sum over allocations of total degree k equals 1 at degree zero and 0 at positive degree when all exponents are zero; otherwise it equals the multichoose coefficient choose(k + total exponent − 1, k).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.allocation_sum_exact_nat
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (e : σ → ℕ) (k : ℕ) :
    (∑ n : σ → Fin (k + 1),
      (if ∑ i, (n i : ℕ) = k then
        ∏ i,
          (if e i = 0 then (if (n i : ℕ) = 0 then 1 else 0)
           else Nat.choose ((n i : ℕ) + e i - 1) (n i : ℕ))
       else 0)) =
      (if ∑ i, e i = 0 then (if k = 0 then 1 else 0)
       else Nat.choose (k + (∑ i, e i) - 1) k) := by sorry
