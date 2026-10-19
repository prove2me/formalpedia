-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_allocation_support_exponent_sum
-- name    : OAI.PiExponent.LiteralAnalytic.allocation_support_exponent_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T18:13:38.919298+00:00
-- url     : https://prove2.me/theorems/82756b2b-cf51-435e-a837-1cd261c90c4e
-- title:
--   Preserve the total exponent on the positive support
-- statement:
--   The sum of a finite family of natural exponents equals its sum over the nonzero support. When the support is empty, both sums are zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic
import Definitions.Def_allocationSum

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.allocation_support_exponent_sum
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (e : σ → ℕ) :
    (∑ i : {j : σ // e j ≠ 0}, e i.1) = ∑ i, e i := by sorry
