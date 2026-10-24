-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_prod_scale_log
-- name    : OAI.PiExponent.DeterminantContradiction.prod_scale_log
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:19:55.796815+00:00
-- url     : https://prove2.me/theorems/c22428d3-b49e-4ea9-b485-3231940eaa46
-- title:
--   Bound the log of a positive scale product
-- statement:
--   Positive natural row scales have a positive product, and the logarithm of that product is bounded by the sum of their logarithms. For an empty index type, the product is one and the logarithmic sum is zero.

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.prod_scale_log
    {α : Type} [Fintype α] [DecidableEq α]
    (scale : α → Nat) (hscale_pos : ∀ i, 0 < scale i)
    (B : Real) (hbudget : (∑ i : α, Real.log (scale i : Real)) ≤ B) :
    0 < ∏ i : α, scale i ∧
      Real.log ((∏ i : α, scale i : Nat) : Real) ≤ B := by
  sorry
