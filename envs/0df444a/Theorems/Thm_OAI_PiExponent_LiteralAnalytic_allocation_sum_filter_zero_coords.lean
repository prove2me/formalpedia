-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_allocation_sum_filter_zero_coords
-- name    : OAI.PiExponent.LiteralAnalytic.allocation_sum_filter_zero_coords
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T18:20:04.897714+00:00
-- url     : https://prove2.me/theorems/e0c968ff-4e94-4a04-92cb-738ec46d72c4
-- title:
--   Filter allocations at zero-exponent coordinates
-- statement:
--   The allocation sum is unchanged when allocations that assign a nonzero degree to a zero-exponent coordinate are discarded.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic
import Definitions.Def_allocationSum
import Definitions.Def_allocationWeight

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.allocation_sum_filter_zero_coords
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (e : σ → ℕ) (k : ℕ) :
    OAI.PiExponent.LiteralAnalytic.allocationSum e k =
      ∑ n : {n : σ → Fin (k + 1) // ∀ i, e i = 0 → n i = 0},
        OAI.PiExponent.LiteralAnalytic.allocationWeight e k n.1 := by sorry
