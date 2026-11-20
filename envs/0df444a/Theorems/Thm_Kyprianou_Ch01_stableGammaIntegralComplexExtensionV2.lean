-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaIntegralComplexExtensionV2
-- name    : Kyprianou.Ch01.stableGammaIntegralComplexExtensionV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T14:23:11.164802+00:00
-- url     : https://prove2.me/theorems/4110e78b-2666-4a42-b3fb-b3d52fbf705f
-- title:
--   Exercise 1.4(i): complex extension of the fractional gamma integral
-- statement:
--   Prove the full complex analytic-extension identity required in Exercise 1.4(i), including nonzero imaginary arguments.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.4(i), printed pp. 27–28, complex continuation following the real gamma identity.

import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

theorem Kyprianou.Ch01.stableGammaIntegralComplexExtensionV2
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hw : w ≠ 0) (hwre : w.re ≤ 0) :
    IntegrableOn
      (fun r : ℝ =>
        (Complex.exp (w * (r : ℂ)) - 1) *
          ((r ^ (-alpha - 1) : ℝ) : ℂ))
      (Set.Ioi (0 : ℝ)) ∧
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (w * (r : ℂ)) - 1) *
        (((r ^ (-alpha - 1) : ℝ)) : ℂ) ∂volume) =
      ((Real.Gamma (-alpha) : ℝ) : ℂ) *
        Complex.exp ((alpha : ℂ) * Complex.log (-w)) := by
  sorry
