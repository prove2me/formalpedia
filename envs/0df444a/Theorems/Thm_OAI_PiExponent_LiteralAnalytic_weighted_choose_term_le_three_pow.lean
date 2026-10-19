-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_weighted_choose_term_le_three_pow
-- name    : OAI.PiExponent.LiteralAnalytic.weighted_choose_term_le_three_pow
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T13:05:09.947144+00:00
-- url     : https://prove2.me/theorems/9ceb652b-2ca9-4a8e-ac4f-0493b995f781
-- title:
--   Weighted binomial term bounded by a power of three
-- statement:
--   For every k ≤ n, the weighted binomial term choose(n,k)·2^k is at most 3^n.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic

theorem OAI.PiExponent.LiteralAnalytic.weighted_choose_term_le_three_pow
    (n k : ℕ) (hk : k ≤ n) :
    n.choose k * 2 ^ k ≤ 3 ^ n := by sorry
