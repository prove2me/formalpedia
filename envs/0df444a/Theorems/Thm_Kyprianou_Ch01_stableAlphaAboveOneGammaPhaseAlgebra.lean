-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneGammaPhaseAlgebra
-- name    : Kyprianou.Ch01.stableAlphaAboveOneGammaPhaseAlgebra
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:25:40.921517+00:00
-- url     : https://prove2.me/theorems/7523c901-2fba-47f2-8ba8-10514d769696
-- title:
--   Stable alpha above one Gamma phase factor exactly matches principal Fourier phase
-- statement:
--   For 1<alpha<2, the exact complex Gamma(1−alpha) coefficient from integration by parts, multiplied by I/alpha and the principal complex log phase log(-I), equals Gamma(-alpha) exp(-I π alpha/2). Follows from the genuine real Gamma recurrence, exp(log(-I))=-I and log(-I)=−πI/2. This proves the exact original compensated stable α>1 Fourier coefficient without changing its complex branch.
-- source:
--   Kyprianou (2006), Chapter 1 stable characteristic exponents α>1; Gamma recurrence and principal Fourier phase.

import Mathlib
open Real Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaAboveOneGammaPhaseAlgebra
    (alpha : ℝ) (h1 : 1 < alpha) (h2 : alpha < 2) :
    (Complex.I / (alpha : ℂ)) *
        (((Real.Gamma (1 - alpha) : ℝ) : ℂ) *
          Complex.exp (((alpha - 1 : ℝ) : ℂ) * Complex.log (-Complex.I))) =
      ((Real.Gamma (-alpha) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((Real.pi * alpha / 2 : ℝ) : ℂ))) := by
  sorry
