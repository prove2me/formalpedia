-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaImaginaryDampingNormTail
-- name    : Kyprianou.Ch01.stableGammaImaginaryDampingNormTail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:10:50.905189+00:00
-- url     : https://prove2.me/theorems/c3d96669-8a62-4ccd-8b07-c5c993f40fde
-- title:
--   Exact damped complex Gamma Fourier kernel Tail norm estimate
-- statement:
--   For pure imaginary w, epsilon≥0 and x>1, the damped exponential has norm at most one, its difference from one is at most two, and ‖w‖+2≥2. Multiplication by x^(−alpha−1) gives the uniform integrable tail envelope.
-- source:
--   Kyprianou (2006) Chapter 1 stable α∈(0,1) complex Gamma Fourier density, uniform damping envelope.

import Mathlib
open MeasureTheory Set Complex Real Filter
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaImaginaryDampingNormTail
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hwre : w.re = 0) (epsilon x : ℝ)
    (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 1) (hx : 0 < x)
    (hx1 : 1 < x) :
    ‖(Complex.exp ((w - (epsilon : ℂ)) * (x : ℂ)) - 1) *
        (((x ^ (-alpha - 1) : ℝ)) : ℂ)‖ ≤
      (‖w‖ + 2) * x ^ (-alpha - 1) := by
  sorry
