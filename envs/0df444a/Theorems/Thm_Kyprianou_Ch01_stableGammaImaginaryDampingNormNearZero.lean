-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaImaginaryDampingNormNearZero
-- name    : Kyprianou.Ch01.stableGammaImaginaryDampingNormNearZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:10:47.629063+00:00
-- url     : https://prove2.me/theorems/02b62198-f7da-47c0-a949-8f39a7b715f4
-- title:
--   Exact damped complex Gamma Fourier kernel NearZero norm estimate
-- statement:
--   For pure imaginary w, 0≤epsilon≤1 and 0<x≤1, the exact damped Fourier difference is at most (‖w‖+2)*x. Split the exponential into real decay and imaginary oscillation, using Mathlib norm_exp_sub_one_le plus the proved imaginary-axis Lipschitz lemma. Multiplication by x^(−alpha−1) gives the source envelope.
-- source:
--   Kyprianou (2006) Chapter 1 stable α∈(0,1) complex Gamma Fourier density, uniform damping envelope.

import Mathlib
open MeasureTheory Set Complex Real Filter
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaImaginaryDampingNormNearZero
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hwre : w.re = 0) (epsilon x : ℝ)
    (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 1) (hx : 0 < x)
    (hx1 : x ≤ 1) :
    ‖(Complex.exp ((w - (epsilon : ℂ)) * (x : ℂ)) - 1) *
        (((x ^ (-alpha - 1) : ℝ)) : ℂ)‖ ≤
      (‖w‖ + 2) * x ^ (-alpha) := by
  sorry
