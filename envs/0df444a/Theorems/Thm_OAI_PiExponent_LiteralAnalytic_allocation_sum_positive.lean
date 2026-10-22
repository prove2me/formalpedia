-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_allocation_sum_positive
-- name    : OAI.PiExponent.LiteralAnalytic.allocation_sum_positive
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T18:14:01.414116+00:00
-- url     : https://prove2.me/theorems/7ee24706-a632-4fee-a841-52850e015fa0
-- title:
--   Evaluate the allocation sum for positive exponents
-- statement:
--   For a finite family of strictly positive exponents with total E, the allocation sum is choose(k + E − 1, k) when E is positive. The family may be empty; then the value is one at degree zero and zero at positive degrees.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic
import Definitions.Def_allocationSum

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.allocation_sum_positive
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (e : σ → ℕ) (k : ℕ) (he : ∀ i, 0 < e i) :
    OAI.PiExponent.LiteralAnalytic.allocationSum e k =
      (if ∑ i, e i = 0 then (if k = 0 then 1 else 0)
       else Nat.choose (k + (∑ i, e i) - 1) k) := by sorry
