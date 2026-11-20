-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitValueImaginary
-- name    : Kyprianou.Ch01.stableGammaComplexDeficitValueImaginary
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:12:26.497208+00:00
-- url     : https://prove2.me/theorems/7afd5413-cc88-4a84-80f5-3fd6c6fd2717
-- title:
--   Stable Gamma complex integral on the nonzero imaginary axis
-- statement:
--   Exact complex Gamma stable-deficit formula for pure nonzero imaginary w. Intended proof by dominated boundary convergence from the strict left half-plane, using the proved complex stable-integrability majorant and principal logarithm continuity away from the branch cut.
-- source:
--   Kyprianou 2006 Chapter 1 stable Gamma identity in closed left half plane; exact subcases of nonreal analytic extension.

import Mathlib
open MeasureTheory Set Complex Real Filter
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaComplexDeficitValueImaginary
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hw : w ≠ 0) (hwre : w.re = 0) (hwim : w.im ≠ 0) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (w * (r : ℂ)) - 1) *
        ((r ^ (-alpha - 1) : ℝ) : ℂ) ∂volume) =
      ((Real.Gamma (-alpha) : ℝ) : ℂ) *
        Complex.exp ((alpha : ℂ) * Complex.log (-w)) := by
  sorry
