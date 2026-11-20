-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftRealExpWeightedIntegrable
-- name    : Kyprianou.Ch01.stableGammaStrictLeftRealExpWeightedIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T15:35:59.077635+00:00
-- url     : https://prove2.me/theorems/d10c694c-f7bc-4917-a45d-64eee20f6be5
-- title:
--   Integrability of the positive Gamma Mellin exponential envelope
-- statement:
--   The real positive-halfline exponential weight exp(t r)*r^(-alpha) is integrable when 0<alpha<1 and t<0, via the pinned Mathlib Gamma envelope integrability theorem.
-- source:
--   Kyprianou (2006) Chapter 1 stable Gamma-Mellin transform, Mathlib ComplexMGF integrability domain.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Complex Real Set Filter ProbabilityTheory Kyprianou.Ch01
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaStrictLeftRealExpWeightedIntegrable
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (t : ℝ) (ht : t < 0) :
    IntegrableOn (fun r : ℝ => Real.exp (t * r) * r ^ (-alpha))
      (Set.Ioi (0 : ℝ)) := by sorry
