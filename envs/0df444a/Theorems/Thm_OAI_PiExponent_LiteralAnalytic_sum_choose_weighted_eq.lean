-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_sum_choose_weighted_eq
-- name    : OAI.PiExponent.LiteralAnalytic.sum_choose_weighted_eq
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:02:15.658548+00:00
-- url     : https://prove2.me/theorems/c4b5947f-43ae-4ce1-81e7-356ed65dc1e8
-- title:
--   Shifted binomial coefficient sum identity
-- statement:
--   For natural k ≥ 1, summing the shifted binomial coefficients from degree 0 through n gives the binomial coefficient choose(n+k,n), by the hockey-stick identity.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Data.Nat.Choose.Sum

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.sum_choose_weighted_eq
    (k n : ℕ) (hk : 1 ≤ k) :
    ∑ r ∈ Finset.range (n + 1), Nat.choose (r + k - 1) r =
      Nat.choose (n + k) n := by sorry
