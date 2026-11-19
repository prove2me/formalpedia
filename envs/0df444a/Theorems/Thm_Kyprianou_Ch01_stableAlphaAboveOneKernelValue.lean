-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneKernelValue
-- name    : Kyprianou.Ch01.stableAlphaAboveOneKernelValue
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T00:15:33.524947+00:00
-- url     : https://prove2.me/theorems/9ac5558c-a7ff-40f3-b4c6-3c0967724bcd
-- title:
--   Stable compensated index alpha above one has exact complex Gamma phase
-- statement:
--   Exact complex Fourier–Gamma integral for 1<alpha<2 with the compensated linear term and the source principal branch phase. Requires the true oscillatory integral identity without adding any assumptions.
-- source:
--   Kyprianou (2006), Chapter 1 stable characteristic exponent for index alpha in (1,2); exact conjunct of stableAlphaAboveOneIntegral.

import Mathlib
open MeasureTheory Set Complex Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaAboveOneKernelValue
    (alpha : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) / ((((r : ℝ) ^ (alpha + 1)) : ℝ) : ℂ)
      ∂volume) =
      ((Real.Gamma (-alpha) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((Real.pi * alpha / 2) : ℂ))) := by
  sorry
