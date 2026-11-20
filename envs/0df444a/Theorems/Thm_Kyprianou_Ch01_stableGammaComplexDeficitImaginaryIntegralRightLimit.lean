-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitImaginaryIntegralRightLimit
-- name    : Kyprianou.Ch01.stableGammaComplexDeficitImaginaryIntegralRightLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:51:42.221181+00:00
-- url     : https://prove2.me/theorems/f651c7c7-a1bd-402a-bbdd-ec48f8b361bc
-- title:
--   Stable complex Gamma deficit integral converges as left damping vanishes (damping limit)
-- statement:
--   For 0<alpha<1 and nonzero imaginary w, the original complex Gamma deficit integral converges under vanishing positive exponential damping w−epsilon, epsilon↓0. This is the exact dominated-convergence step from the strict left half-plane integral to the imaginary boundary.
-- source:
--   Kyprianou (2006), Chapter 1 stable α∈(0,1) complex Gamma integral at nonzero imaginary parameters, strict-left limit.

import Mathlib
open MeasureTheory Set Complex Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaComplexDeficitImaginaryIntegralRightLimit
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hw : w ≠ 0) (hwre : w.re = 0) (hwim : w.im ≠ 0) :
    Tendsto
      (fun epsilon : ℝ =>
        (∫ r in Set.Ioi (0 : ℝ),
          (Complex.exp ((w - (epsilon : ℂ)) * (r : ℂ)) - 1) *
            (((r ^ (-alpha - 1) : ℝ)) : ℂ)
          ∂volume))
      ((nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))))
      (nhds (∫ r in Set.Ioi (0 : ℝ),
        (Complex.exp (w * (r : ℂ)) - 1) *
          (((r ^ (-alpha - 1) : ℝ)) : ℂ)
        ∂volume)) := by
  sorry
