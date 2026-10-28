-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_allocation_sum_support_reindex
-- name    : OAI.PiExponent.LiteralAnalytic.allocation_sum_support_reindex
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T18:20:31.297407+00:00
-- url     : https://prove2.me/theorems/6afe8824-98d0-4f98-a82b-9ec336acd44e
-- title:
--   Reindex filtered allocations on the positive support
-- statement:
--   Reindex allocations on the full type that vanish outside the positive support as allocations on the positive-support subtype.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic
import Definitions.Def_allocationSum
import Definitions.Def_allocationWeight

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.allocation_sum_support_reindex
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (e : σ → ℕ) (k : ℕ) :
    (∑ n : {n : σ → Fin (k + 1) // ∀ i, e i = 0 → n i = 0},
      OAI.PiExponent.LiteralAnalytic.allocationWeight e k n.1) =
      OAI.PiExponent.LiteralAnalytic.allocationSum
        (fun i : {j : σ // e j ≠ 0} => e i.1) k := by sorry
