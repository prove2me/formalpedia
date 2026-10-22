-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_coeff_mul_norm_le_choose_weighted_succ_general
-- name    : OAI.PiExponent.LiteralAnalytic.coeff_mul_norm_le_choose_weighted_succ_general
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T16:56:43.875609+00:00
-- url     : https://prove2.me/theorems/d53939a2-c196-4188-a5c9-aca900aa66a4
-- title:
--   Weighted coefficient bound for a product of power series
-- statement:
--   For nonnegative C and k ≥ 1, if the coefficients of f satisfy the degree-r binomial bound with scale C^k and the coefficients of g are bounded by C, then the degree-n coefficient of f*g satisfies the successor binomial bound.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Order

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.coeff_mul_norm_le_choose_weighted_succ_general
    (f g : PowerSeries ℂ) (k n : ℕ) (C : ℝ)
    (hC : 0 ≤ C)
    (hf : ∀ r, ‖PowerSeries.coeff r f‖ ≤
      C ^ k * (Nat.choose (r + k - 1) r : ℝ))
    (hg : ∀ r, ‖PowerSeries.coeff r g‖ ≤ C)
    (hk : 1 ≤ k) :
    ‖PowerSeries.coeff n (f * g)‖ ≤
      C ^ (k + 1) * (Nat.choose (n + (k + 1) - 1) n : ℝ) := by
  sorry
