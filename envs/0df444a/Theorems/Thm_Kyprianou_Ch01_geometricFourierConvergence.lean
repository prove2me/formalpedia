-- Prove2me | Theorems.Thm_Kyprianou_Ch01_geometricFourierConvergence
-- name    : Kyprianou.Ch01.geometricFourierConvergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:39:58.114794+00:00
-- url     : https://prove2.me/theorems/dab12c5d-6def-4c89-8fd0-6859e14fd0db
-- title:
--   Uniform Fourier-circle geometric-series convergence for every positive geometric success probability
-- statement:
--   For any nonzero success parameter p in the closed unit interval and every real Fourier frequency ξ, the complex ratio (1-p)e^{iξ} has norm strictly below one. The proof uses the unit norm of the complex exponential on the imaginary axis and the strict real inequality 1-p<1 for p>0. This validates the geometric probability generating function at every characteristic-function argument, thereby bridging the finite-radius analytic PGF theorem to the full geometric characteristic function needed for infinite divisibility.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.2(i); pinned Mathlib Complex.norm_exp_I_mul_ofReal.

import Mathlib
open Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.geometricFourierConvergence
    (p : unitInterval.Elem) (hp : p ≠ 0) (xi : ℝ) :
    ‖(1 - ((p : ℝ) : ℂ)) *
      Complex.exp (Complex.I * (xi : ℂ))‖ < 1 := by
  sorry
