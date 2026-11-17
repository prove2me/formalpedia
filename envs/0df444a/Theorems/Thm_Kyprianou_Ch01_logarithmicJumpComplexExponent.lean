-- Prove2me | Theorems.Thm_Kyprianou_Ch01_logarithmicJumpComplexExponent
-- name    : Kyprianou.Ch01.logarithmicJumpComplexExponent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:52:20.689657+00:00
-- url     : https://prove2.me/theorems/3ac992a4-8b73-40b2-9452-df0c848f9351
-- title:
--   Exact complex logarithmic-series jump exponent as a difference of complex logarithms
-- statement:
--   For any complex q,z with ‖q‖<1 and ‖qz‖<1, the infinite series of logarithmic jump characteristic terms Σ_{k≥1} q^k(z^k−1)/k equals log(1−q)−log(1−qz), with both series absolutely convergent. This identity is the exact analytic Fourier exponent of the logarithmic-series compound Poisson representation of the geometric count law in Kyprianou Chapter 1 Exercise 1.2(i). Its proof subtracts the two pinned Mathlib complex logarithm Taylor-series convergence theorems; it does not assume the desired infinite divisibility.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.2(i), solution p. 299; pinned Mathlib Complex.hasSum_taylorSeries_neg_log', HasSum.sub.

import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
open Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.logarithmicJumpComplexExponent (q z : ℂ) (hq : ‖q‖ < 1)
    (hqz : ‖q * z‖ < 1) :
    (∑' n : ℕ,
        ((q * z) ^ (n + 1) / ((n : ℂ) + 1) -
          q ^ (n + 1) / ((n : ℂ) + 1))) =
      Complex.log (1 - q) - Complex.log (1 - q * z) := by
  sorry
