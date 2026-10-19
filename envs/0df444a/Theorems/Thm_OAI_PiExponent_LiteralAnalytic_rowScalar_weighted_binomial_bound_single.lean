-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_rowScalar_weighted_binomial_bound_single
-- name    : OAI.PiExponent.LiteralAnalytic.rowScalar_weighted_binomial_bound_single
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T12:56:03.50642+00:00
-- url     : https://prove2.me/theorems/e02e921c-a22b-4c91-90a8-7faa20f80103
-- title:
--   Single row weighted binomial bound
-- statement:
--   For one row, the product of the two binomial coefficients and the weight `2^e` is bounded by `4^a`. The Fin bound ensures `e ≤ a-b`; if `b > a`, the first binomial coefficient is zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.rowScalar_weighted_binomial_bound_single
    (a b : ℕ) (e : Fin (a - b + 1)) :
    (((a.choose b * (a - b).choose (e : ℕ) : ℕ) : ℝ) *
      (2 : ℝ) ^ (e : ℕ)) ≤ (4 : ℝ) ^ a := by sorry
