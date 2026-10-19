-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_coeff_pow_norm_le_choose_weighted_succ
-- name    : OAI.PiExponent.LiteralAnalytic.coeff_pow_norm_le_choose_weighted_succ
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T16:44:50.741352+00:00
-- url     : https://prove2.me/theorems/9bd43907-513d-48f8-82a9-22c06c419487
-- title:
--   Successor step for the power-series coefficient bound
-- statement:
--   If the degree-r coefficients of τ^k satisfy the claimed binomial bound for every r, and the coefficients of τ are bounded by nonnegative C, then the degree-n coefficient of τ^(k+1) satisfies the corresponding successor bound. The condition k ≥ 1 keeps the binomial indices in the intended nonnegative range; the lemma also includes the C = 0 boundary case.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Order

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.coeff_pow_norm_le_choose_weighted_succ
    (τ : PowerSeries ℂ) (k n : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hτc : ∀ r, ‖PowerSeries.coeff r τ‖ ≤ C)
    (hk : 1 ≤ k)
    (hpow : ∀ r, ‖PowerSeries.coeff r (τ ^ k)‖ ≤
      C ^ k * (Nat.choose (r + k - 1) r : ℝ)) :
    ‖PowerSeries.coeff n (τ ^ (k + 1))‖ ≤
      C ^ (k + 1) * (Nat.choose (n + (k + 1) - 1) n : ℝ) := by
  sorry
