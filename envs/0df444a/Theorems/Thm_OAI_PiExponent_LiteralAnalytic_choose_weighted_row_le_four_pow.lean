-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_choose_weighted_row_le_four_pow
-- name    : OAI.PiExponent.LiteralAnalytic.choose_weighted_row_le_four_pow
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T13:05:31.457455+00:00
-- url     : https://prove2.me/theorems/6e1a7b5b-5f3a-4321-a981-5a79c53cc0ff
-- title:
--   Weighted row binomial term bounded by a power of four
-- statement:
--   For all natural numbers a and b, choose(a,b)·3^(a-b) is at most 4^a; the left side vanishes when b > a.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic

theorem OAI.PiExponent.LiteralAnalytic.choose_weighted_row_le_four_pow
    (a b : ℕ) :
    a.choose b * 3 ^ (a - b) ≤ 4 ^ a := by sorry
