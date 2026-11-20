-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianJumpCompensatorIntegrable
-- name    : Kyprianou.Ch01.inverseGaussianJumpCompensatorIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:37:43.914968+00:00
-- url     : https://prove2.me/theorems/2f41f0bf-033b-47ce-8a07-7475a77f9921
-- title:
--   Inverse-Gaussian Lévy jump characteristic integrand is integrable
-- statement:
--   For the exact inverse-Gaussian Lévy measure and any Fourier frequency theta, 1-exp(i theta x) is integrable on positive jumps. Near zero the numerator is O(x) and density O(x^(-3/2)), while exponential tilt dominates the tail.
-- source:
--   Kyprianou (2006), Chapter 1 inverse-Gaussian Lévy exponent and Lévy measure, source-exact child.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Set Complex ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianJumpCompensatorIntegrable
    (b : ℝ) (hb : 0 < b) :
    let Pi : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-(b ^ 2 * x / 2))))
    ∀ theta : ℝ,
      IntegrableOn
        (fun x : ℝ => (1 - Complex.exp
            (Complex.I * ((theta * x : ℝ) : ℂ))))
        (Set.Ioi (0 : ℝ)) Pi := by
  sorry
