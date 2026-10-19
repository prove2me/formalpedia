-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_coeff_pow_norm_le_choose_weighted
-- name    : OAI.PiExponent.LiteralAnalytic.coeff_pow_norm_le_choose_weighted
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T16:38:28.646048+00:00
-- url     : https://prove2.me/theorems/0f911b1d-15c3-40ea-b5f0-33d7ac8d7db3
-- title:
--   Coefficient bound for a power of a power series
-- statement:
--   If all coefficients of a power series have norm at most a nonnegative real C, then the degree-n coefficient of its m-th power is bounded by C^m times the number of weak allocations of degree n among m factors. The exponent-zero case records that the zeroth power has no positive-degree coefficients.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Order

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.coeff_pow_norm_le_choose_weighted
    (τ : PowerSeries ℂ) (m n : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hτc : ∀ r, ‖PowerSeries.coeff r τ‖ ≤ C) :
    ‖PowerSeries.coeff n (τ ^ m)‖ ≤
      C ^ m *
        (if m = 0 then (if n = 0 then (1 : ℝ) else 0)
         else (Nat.choose (n + m - 1) n : ℝ)) := by
  sorry
