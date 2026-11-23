-- Prove2me | Theorems.Thm_Kyprianou_Ch01_smallPositivePowerSeriesTailHasSum
-- name    : Kyprianou.Ch01.smallPositivePowerSeriesTailHasSum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T07:33:24.035095+00:00
-- url     : https://prove2.me/theorems/90c15ca7-1cbc-4e47-9a56-7e787858d3dd
-- title:
--   Shifted tail sum isolates a leading power-series coefficient
-- statement:
--   If the real power series ∑ z^n a_n vanishes at each small positive z and the coefficients below k are zero, then the shifted tail ∑ z^(i+1) a_(i+k+1) converges to −a_k for each small z. Isolate the finite prefix with hasSum_nat_add_iff, then divide by positive z^k. No absolute-summability premise is needed beyond the given HasSum at z.
-- source:
--   Directly adapted from the actual Proved AvramDividend.Classical.avram_a27_real_exponential_pgf_hasSum_unique_power_series_coefficients_20261117, helper PgfAux.coeff_zero.

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.smallPositivePowerSeriesTailHasSum
    (a : ℕ → ℝ)
    (h : ∀ z : ℝ, 0 < z → z ≤ (1/2 : ℝ) →
        HasSum (fun n : ℕ => z ^ n * a n) 0)
    (k : ℕ) (hprefix : ∀ i : ℕ, i < k → a i = 0)
    (z : ℝ) (hz : 0 < z) (hz2 : z ≤ (1/2 : ℝ)) :
    HasSum (fun i : ℕ => z ^ (i + 1) * a (i + (k + 1))) (-(a k)) := by
  sorry
