-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftIBPProductIntegrable
-- name    : Kyprianou.Ch01.stableGammaStrictLeftIBPProductIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:19:37.591821+00:00
-- url     : https://prove2.me/theorems/20acdd4e-19ba-4cb9-8a45-abadd81644ec
-- title:
--   Both exact strict-left Gamma integration-by-parts products are integrable
-- statement:
--   The first product is the already Proved stableGammaComplexDeficitIntegrable source kernel; the second is a fixed complex scalar (−w/alpha) times the strict-left Mellin kernel, whose integral is integrable by the new Gamma Mellin integrability proof.
-- source:
--   Kyprianou (2006), Chapter 1, complex stable Gamma deficit integral, source exact analytic half-line integration by parts.

import Mathlib
open MeasureTheory Complex Real Set Filter
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaStrictLeftIBPProductIntegrable
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hwre : w.re < 0) :
    IntegrableOn
      (fun r : ℝ => (Complex.exp (w * (r : ℂ)) - 1) * (((r ^ (-alpha - 1) : ℝ)) : ℂ))
      (Set.Ioi (0 : ℝ)) ∧
    IntegrableOn
      (fun r : ℝ => (w * Complex.exp (w * (r : ℂ))) * (((r ^ (-alpha) / (-alpha) : ℝ)) : ℂ))
      (Set.Ioi (0 : ℝ)) := by sorry
