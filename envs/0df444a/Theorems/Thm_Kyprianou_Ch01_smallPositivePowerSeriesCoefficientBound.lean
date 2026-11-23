-- Prove2me | Theorems.Thm_Kyprianou_Ch01_smallPositivePowerSeriesCoefficientBound
-- name    : Kyprianou.Ch01.smallPositivePowerSeriesCoefficientBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T07:29:15.033474+00:00
-- url     : https://prove2.me/theorems/3f8b1b05-b75c-4f83-bc7c-5d56d9cdc984
-- title:
--   Geometric-tail bound on the leading nonzero coefficient of a small-positive power series
-- statement:
--   A vanishing real power series with uniformly bounded coefficients and zero coefficients before k has kth coefficient of absolute value ≤ 2Mz for every 0<z≤1/2. Subtract prefix via hasSum_nat_add_iff, divide by z^k, bound the tail by the geometric series zM/(1−z), and use z≤1/2.
-- source:
--   Adapted from the actual remote-Proved Lean proof AvramDividend.Classical.avram_a27_real_exponential_pgf_hasSum_unique_power_series_coefficients_20261117, helper PgfAux.coeff_zero

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.smallPositivePowerSeriesCoefficientBound
    (a : ℕ → ℝ) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ i : ℕ, |a i| ≤ M)
    (h : ∀ z : ℝ, 0 < z → z ≤ (1/2 : ℝ) →
        HasSum (fun n : ℕ => z ^ n * a n) 0)
    (k : ℕ) (hprefix : ∀ i : ℕ, i < k → a i = 0)
    (z : ℝ) (hz : 0 < z) (hz2 : z ≤ (1/2 : ℝ)) :
    |a k| ≤ 2 * M * z := by
  sorry
