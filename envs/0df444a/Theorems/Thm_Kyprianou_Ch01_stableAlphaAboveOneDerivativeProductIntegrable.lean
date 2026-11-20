-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneDerivativeProductIntegrable
-- name    : Kyprianou.Ch01.stableAlphaAboveOneDerivativeProductIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:18:18.77189+00:00
-- url     : https://prove2.me/theorems/d21fd3cf-a250-44d9-ac00-c3c46a0ef655
-- title:
--   Integrability of the reduced stable Fourier derivative times negative-power antiderivative
-- statement:
--   The source exact derivative×antiderivative term i(exp(ir)−1)r^(−alpha)/(−alpha) is a constant complex multiple of the already Proved integrable reduced Fourier kernel.
-- source:
--   Kyprianou (2006), Chapter 1 compensated α>1 Fourier integral, source-exact half-line integration by parts.

import Mathlib
open MeasureTheory Set Complex Real Filter
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaAboveOneDerivativeProductIntegrable
    (alpha : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    IntegrableOn
      (fun r : ℝ =>
        (Complex.I * (Complex.exp (Complex.I * (r : ℂ)) - 1)) *
          (((r ^ (-alpha) / (-alpha) : ℝ)) : ℂ))
      (Set.Ioi (0 : ℝ)) := by sorry
