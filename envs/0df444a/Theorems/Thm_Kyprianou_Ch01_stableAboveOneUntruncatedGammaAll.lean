-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAboveOneUntruncatedGammaAll
-- name    : Kyprianou.Ch01.stableAboveOneUntruncatedGammaAll
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:14:39.81927+00:00
-- url     : https://prove2.me/theorems/01dd47b9-9c16-4804-9bd0-990fdf743681
-- title:
--   All-frequency above-one untruncated stable Fourier Gamma integral
-- statement:
--   For 1<alpha<2 and any real xi, the positive-halfline untruncated compensated Fourier integral is the principal Gamma fractional-power expression, with value zero at xi=0. Positive xi follows from scaling; negative xi follows by complex conjugation.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4.

import Mathlib
open MeasureTheory Set Real Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAboveOneUntruncatedGammaAll
 (alpha xi : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
 (∫ r in Set.Ioi (0 : ℝ),
   (Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) - 1 -
    Complex.I * (((xi * r : ℝ) : ℂ))) /
   (((r ^ (alpha + 1) : ℝ) : ℂ)) ∂volume) =
 (if xi = 0 then (0 : ℂ) else
   (((Real.Gamma (-alpha) : ℝ) : ℂ)) *
     Complex.exp ((alpha : ℂ) *
       Complex.log (-(Complex.I * (xi : ℂ))))) := by sorry
