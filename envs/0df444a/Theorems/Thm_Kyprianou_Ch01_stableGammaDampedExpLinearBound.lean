-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaDampedExpLinearBound
-- name    : Kyprianou.Ch01.stableGammaDampedExpLinearBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:14:00.239334+00:00
-- url     : https://prove2.me/theorems/8c06c23e-a42c-4c55-93be-a82161843ab4
-- title:
--   Uniform small-argument linear bound for exponentially damped imaginary Fourier kernel
-- statement:
--   For pure imaginary w, 0≤epsilon≤1 and 0<x≤1, the exact damped Fourier difference exp((w−epsilon)x)−1 has norm at most (|w|+2)x. Separate the unit-modulus imaginary exponential from the real exponential damping; the former has the sharp |w|x bound, while the latter has the uniform 2 epsilon x bound by Mathlib norm_exp_sub_one_le because epsilon x≤1. This provides the genuine near-origin analytic step in imaginary-axis Gamma dominated convergence.
-- source:
--   Kyprianou (2006) Chapter 1 stable complex Fourier-Gamma exponent, damping norm at the origin.

import Mathlib
open MeasureTheory Set Complex Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaDampedExpLinearBound
    (w : ℂ) (hwre : w.re = 0) (epsilon x : ℝ)
    (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 1)
    (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖Complex.exp ((w - (epsilon : ℂ)) * (x : ℂ)) - 1‖ ≤
      (‖w‖ + 2) * x := by
  sorry
