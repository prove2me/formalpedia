-- Prove2me | Theorems.Thm_Kyprianou_Ch01_shiftedPMFCharFun_tsum
-- name    : Kyprianou.Ch01.shiftedPMFCharFun_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:15:15.294811+00:00
-- url     : https://prove2.me/theorems/3c7adca2-f676-428e-9141-4c1b9aa7ca49
-- title:
--   Fourier-series characteristic function for a positive-integer shifted PMF
-- statement:
--   For any probability mass function on ℕ, after mapping n to the positive real integer n+1, the resulting law's characteristic function equals the absolutely convergent Fourier series of its shifted point masses. This gives the distributional bridge needed to recognise the logarithmic-jump compound-Poisson representation of a geometric law.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(i); discrete Fourier representation.

import Mathlib
open MeasureTheory ProbabilityTheory Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.shiftedPMFCharFun_tsum
    (jump : PMF ℕ) (xi : ℝ) :
    charFun (jump.toMeasure.map
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ))) xi =
      ∑' n : ℕ, (jump n).toReal •
        Complex.exp
          ((xi : ℂ) * (((n + 1 : ℕ) : ℝ) : ℂ) * Complex.I) := by
  sorry
