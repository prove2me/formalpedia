-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_allocation_sum_support_reduction
-- name    : OAI.PiExponent.LiteralAnalytic.allocation_sum_support_reduction
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T18:13:18.804744+00:00
-- url     : https://prove2.me/theorems/daaa4397-8707-4802-b1d8-bf9a1696fbd2
-- title:
--   Restrict allocation sums to the positive support
-- statement:
--   For any finite family of natural exponents and any natural degree, removing zero-exponent coordinates preserves the allocation sum. This includes empty support and degree zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic
import Definitions.Def_allocationSum

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.allocation_sum_support_reduction
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (e : σ → ℕ) (k : ℕ) :
    OAI.PiExponent.LiteralAnalytic.allocationSum e k =
      OAI.PiExponent.LiteralAnalytic.allocationSum
        (fun i : {j : σ // e j ≠ 0} => e i.1) k := by sorry
