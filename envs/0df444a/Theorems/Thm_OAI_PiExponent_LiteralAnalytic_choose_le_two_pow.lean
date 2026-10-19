-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_choose_le_two_pow
-- name    : OAI.PiExponent.LiteralAnalytic.choose_le_two_pow
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T12:55:40.738401+00:00
-- url     : https://prove2.me/theorems/71e0682a-4905-4bc3-8377-dfab58b3607d
-- title:
--   Bound a binomial coefficient by a power of two
-- statement:
--   A binomial coefficient is bounded by the sum of all binomial coefficients of the same upper index, namely 2 raised to that index.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic

theorem OAI.PiExponent.LiteralAnalytic.choose_le_two_pow (k n : ℕ) :
    (Nat.choose (k + n) k : ℝ) ≤ (2 : ℝ) ^ (k + n) := by sorry
