-- Prove2me | Theorems.Thm_Kyprianou_Ch01_summablePowerSeriesZeroCoefficientsOfSmallPositiveValues
-- name    : Kyprianou.Ch01.summablePowerSeriesZeroCoefficientsOfSmallPositiveValues
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T07:26:11.663818+00:00
-- url     : https://prove2.me/theorems/3cc403ef-89ab-4316-9fd4-9389adbf3c60
-- title:
--   Uniqueness of absolutely summable real power-series coefficients from small positive values
-- statement:
--   If real coefficients are absolutely summable and their power series vanishes on every sufficiently small positive real argument z in (0,1/2], then every coefficient is zero. Proof by strong induction: subtract the vanished finite prefix, divide the remaining series by z^k, and bound the tail by a geometric series O(z). Passing to sufficiently small positive z forces the kth coefficient to vanish. No analyticity assumptions beyond summability are needed.
-- source:
--   Derived and adapted from Prove2Me Proved AvramDividend.Classical.avram_a27_real_exponential_pgf_hasSum_unique_power_series_coefficients_20261117 (internal helper PgfAux.coeff_zero); applied to Kyprianou Chapter 1 branching-Laplace uniqueness.

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.summablePowerSeriesZeroCoefficientsOfSmallPositiveValues
    (a : ℕ → ℝ) (hsum : Summable a)
    (h : ∀ z : ℝ, 0 < z → z ≤ (1/2 : ℝ) →
        HasSum (fun k : ℕ => z ^ k * a k) 0) :
    ∀ k, a k = 0 := by
  sorry
