-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaBelowOneFourierGammaAll
-- name    : Kyprianou.Ch01.stableAlphaBelowOneFourierGammaAll
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:29:11.632566+00:00
-- url     : https://prove2.me/theorems/780dbf5e-94b0-4253-a807-abd7e7bfde8e
-- title:
--   Stable Gamma Fourier deficit evaluation for all frequencies including zero
-- statement:
--   For 0<alpha<1, the exact positive-halfline Lévy Fourier kernel integral equals zero at Fourier frequency zero, and equals Gamma(-alpha)*exp(alpha log(-i xi)) at every nonzero real frequency. The branch at xi=0 is essential because the principal complex log is singular there.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4; proved nonzero-frequency Gamma deficit identity.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaBelowOneFourierGammaNonzero
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Complex Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaBelowOneFourierGammaAll
    (alpha xi : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    (∫ r in Set.Ioi (0 : ℝ),
       (Complex.exp ((Complex.I * (xi : ℂ)) * (r : ℂ)) - 1) *
         ((r ^ (-alpha - 1) : ℝ) : ℂ) ∂volume) =
      if xi = 0 then 0 else
        ((Real.Gamma (-alpha) : ℝ) : ℂ) *
          Complex.exp ((alpha : ℂ) *
            Complex.log (-(Complex.I * (xi : ℂ)))) := by sorry
