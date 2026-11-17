-- Prove2me | Theorems.Thm_Kyprianou_Ch01_logarithmicJumpFourierSummable
-- name    : Kyprianou.Ch01.logarithmicJumpFourierSummable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:24:30.454706+00:00
-- url     : https://prove2.me/theorems/92c1359c-8f9d-4f00-836b-0faebbf1f616
-- title:
--   Absolute summability of the logarithmic-jump Fourier series
-- statement:
--   For q strictly between zero and one, logarithmic jump weights times the unit-modulus Fourier phase are absolutely summable at every real frequency. This convergence justifies compensation and algebraic rearrangement of the compound-Poisson characteristic exponent in Kyprianou's Exercise 1.2(i).
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(i), rigorous Fourier derivation.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_logarithmicJumpWeightsHasSumOne
open Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.logarithmicJumpFourierSummable
    (q xi : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    Summable (fun n : ℕ =>
      (((q ^ (n + 1) / ((n : ℝ) + 1)) /
        (-Real.log (1 - q))) : ℂ) *
        Complex.exp ((xi : ℂ) *
          (((n + 1 : ℕ) : ℝ) : ℂ) * Complex.I)) := by
  sorry
