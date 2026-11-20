-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitValueNonReal
-- name    : Kyprianou.Ch01.stableGammaComplexDeficitValueNonReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:58:52.857378+00:00
-- url     : https://prove2.me/theorems/e9e3a19c-5362-4e91-966e-7caad49d76d3
-- title:
--   Stable Gamma complex deficit integral on nonreal left-half-plane
-- statement:
--   The full principal-branch complex stable Gamma deficit identity for nonreal complex w in the closed left half-plane; both strict left half-plane and imaginary boundary are included. This is the genuinely nonreal analytic extension obligation.
-- source:
--   Kyprianou 2006, Ch1 stable gamma complex Fourier-Laplace integral; exact split of stableGammaComplexDeficitValue.

import Mathlib
open MeasureTheory Set Complex Real Filter
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaComplexDeficitValueNonReal
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hw : w ≠ 0) (hwre : w.re ≤ 0)
    (hwim : w.im ≠ 0) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (w * (r : ℂ)) - 1) *
        ((r ^ (-alpha - 1) : ℝ) : ℂ) ∂volume) =
      ((Real.Gamma (-alpha) : ℝ) : ℂ) *
        Complex.exp ((alpha : ℂ) * Complex.log (-w)) := by
  sorry
