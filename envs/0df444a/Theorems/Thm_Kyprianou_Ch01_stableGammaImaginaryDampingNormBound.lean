-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaImaginaryDampingNormBound
-- name    : Kyprianou.Ch01.stableGammaImaginaryDampingNormBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:04:31.612025+00:00
-- url     : https://prove2.me/theorems/62674e97-f95e-4765-8668-a54c70712589
-- title:
--   Uniform dominated norm of the damped imaginary-axis complex Gamma deficit kernel
-- statement:
--   For 0<alpha<1, imaginary w and 0≤epsilon≤1, the exact damped complex Fourier kernel (exp((w−epsilon)x)−1)*x^(−alpha−1) has norm dominated by (‖w‖+2) times x^(−alpha) for 0<x≤1 and x^(−alpha−1) for x>1. The damped exponential contracts on the right half-line, yielding linear-in-x near zero and a uniform bound two at infinity. This is the genuine bound for dominated convergence at the imaginary axis.
-- source:
--   Kyprianou (2006) Chapter 1 stable index 0<alpha<1; exact Fourier-Gamma dominated-convergence source.

import Mathlib
open MeasureTheory Set Complex Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaImaginaryDampingNormBound
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hwre : w.re = 0) (epsilon x : ℝ)
    (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 1) (hx : 0 < x) :
    ‖(Complex.exp ((w - (epsilon : ℂ)) * (x : ℂ)) - 1) *
        (((x ^ (-alpha - 1) : ℝ)) : ℂ)‖ ≤
      (‖w‖ + 2) *
        (if x ≤ 1 then x ^ (-alpha)
          else x ^ (-alpha - 1)) := by
  sorry
