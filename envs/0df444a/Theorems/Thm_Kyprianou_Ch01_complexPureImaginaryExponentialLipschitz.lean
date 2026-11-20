-- Prove2me | Theorems.Thm_Kyprianou_Ch01_complexPureImaginaryExponentialLipschitz
-- name    : Kyprianou.Ch01.complexPureImaginaryExponentialLipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:05:22.415081+00:00
-- url     : https://prove2.me/theorems/5ae4352b-d7a7-46b2-9353-fdb2cb1bc689
-- title:
--   Complex imaginary-axis exponential difference bounded linearly by imaginary frequency
-- statement:
--   For a pure imaginary complex frequency w and x≥0, the complex unit-modulus exponential satisfies |exp(w x)−1|≤|w| x. This follows from the established Mathlib imaginary-exponential Lipschitz inequality with w=i Im w. It is used in the true uniform ε-damping estimate for the α∈(0,1) Gamma/Fourier integral.
-- source:
--   Kyprianou (2006), Chapter 1 stable Fourier characteristic exponent; imaginary-axis exponential estimate.

import Mathlib
open MeasureTheory Set Complex Real
set_option autoImplicit false

theorem Kyprianou.Ch01.complexPureImaginaryExponentialLipschitz
    (w : ℂ) (hwre : w.re = 0) (x : ℝ) (hx : 0 ≤ x) :
    ‖Complex.exp (w * (x : ℂ)) - 1‖ ≤ ‖w‖ * x := by
  sorry
