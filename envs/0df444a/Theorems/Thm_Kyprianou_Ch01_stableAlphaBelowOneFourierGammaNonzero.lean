-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaBelowOneFourierGammaNonzero
-- name    : Kyprianou.Ch01.stableAlphaBelowOneFourierGammaNonzero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:22:53.533013+00:00
-- url     : https://prove2.me/theorems/81d0705b-36b0-4f62-9106-80fd0b0f36d2
-- title:
--   Source-exact nonzero Fourier kernel at stable index strictly below one
-- statement:
--   For 0<alpha<1 and nonzero Fourier frequency xi, evaluate the positive-halfline stable Lévy jump integral (exp(i xi r)-1)r^(-alpha-1) as Gamma(-alpha)*exp(alpha log(-i xi)) on the principal complex branch. This is the exact Fourier version of the proved complex Gamma deficit theorem.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4, non-unit index Lévy exponent, via proved stableGammaComplexDeficitValue.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitValue
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Complex Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaBelowOneFourierGammaNonzero
    (alpha xi : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (hxi : xi ≠ 0) :
    (∫ r in Set.Ioi (0 : ℝ),
       (Complex.exp ((Complex.I * (xi : ℂ)) * (r : ℂ)) - 1) *
         ((r ^ (-alpha - 1) : ℝ) : ℂ) ∂volume) =
      ((Real.Gamma (-alpha) : ℝ) : ℂ) *
        Complex.exp ((alpha : ℂ) *
          Complex.log (-(Complex.I * (xi : ℂ)))) := by sorry
