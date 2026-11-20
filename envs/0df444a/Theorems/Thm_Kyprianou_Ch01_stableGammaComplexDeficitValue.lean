-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitValue
-- name    : Kyprianou.Ch01.stableGammaComplexDeficitValue
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:50:33.806813+00:00
-- url     : https://prove2.me/theorems/f3b6ff22-10d0-4710-9d2b-4d502f886d1a
-- title:
--   Complex stable Gamma deficit integral has principal-branch fractional power
-- statement:
--   Exact complex Gamma integral identity for nonzero w with nonpositive real part and alpha in (0,1). Principal complex logarithm branch retained, including the imaginary boundary, with no additional assumptions.
-- source:
--   Kyprianou (2006), Chapter 1, stable-index integral and Appendix worked derivation, source-exact part of stableGammaIntegralComplexExtensionV2.

import Mathlib
open MeasureTheory Set Complex Filter
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaComplexDeficitValue
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hw : w ≠ 0) (hwre : w.re ≤ 0) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (w * (r : ℂ)) - 1) *
        (((r ^ (-alpha - 1) : ℝ)) : ℂ) ∂volume) =
      ((Real.Gamma (-alpha) : ℝ) : ℂ) *
        Complex.exp ((alpha : ℂ) * Complex.log (-w)) := by
  sorry
