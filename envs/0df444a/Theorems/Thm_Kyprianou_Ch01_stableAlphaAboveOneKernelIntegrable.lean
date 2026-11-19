-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneKernelIntegrable
-- name    : Kyprianou.Ch01.stableAlphaAboveOneKernelIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:15:32.651693+00:00
-- url     : https://prove2.me/theorems/90e839ec-e754-4f8e-b21d-545b94102024
-- title:
--   Stable compensated index alpha above one has integrable complex kernel
-- statement:
--   Absolute integrability of the unchanged index-alpha stable compensated Fourier kernel for 1<alpha<2. Near zero the numerator is bounded by r² and the denominator r^(alpha+1), giving r^(1-alpha); above one the numerator grows at most linearly, giving r^(-alpha).
-- source:
--   Kyprianou (2006), Chapter 1 stable characteristic exponent for index alpha in (1,2); exact conjunct of stableAlphaAboveOneIntegral.

import Mathlib
open MeasureTheory Set Complex Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaAboveOneKernelIntegrable
    (alpha : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    IntegrableOn
      (fun r : ℝ =>
        (Complex.exp (Complex.I * (r : ℂ)) - 1 -
          Complex.I * (r : ℂ)) /
            ((((r : ℝ) ^ (alpha + 1)) : ℝ) : ℂ))
      (Set.Ioi (0 : ℝ)) := by
  sorry
