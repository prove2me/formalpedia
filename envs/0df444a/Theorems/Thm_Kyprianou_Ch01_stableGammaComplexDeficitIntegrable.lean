-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitIntegrable
-- name    : Kyprianou.Ch01.stableGammaComplexDeficitIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:50:33.680995+00:00
-- url     : https://prove2.me/theorems/132e16b5-84b1-452d-bf95-0308256567a3
-- title:
--   Complex stable Gamma deficit is integrable on the positive half-line
-- statement:
--   Absolute integrability of the complex exponential deficit kernel for alpha in (0,1) and nonzero complex w in the closed left half-plane. At zero the deficit is O(r); at infinity exp(wr) is bounded by one, allowing power comparison.
-- source:
--   Kyprianou (2006), Chapter 1, stable-index integral and Appendix worked derivation, source-exact part of stableGammaIntegralComplexExtensionV2.

import Mathlib
open MeasureTheory Set Complex Filter
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaComplexDeficitIntegrable
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hw : w ≠ 0) (hwre : w.re ≤ 0) :
    IntegrableOn
      (fun r : ℝ =>
        (Complex.exp (w * (r : ℂ)) - 1) *
          ((r ^ (-alpha - 1) : ℝ) : ℂ))
      (Set.Ioi (0 : ℝ)) := by
  sorry
