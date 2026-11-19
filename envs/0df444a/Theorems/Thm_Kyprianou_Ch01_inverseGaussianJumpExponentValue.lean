-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianJumpExponentValue
-- name    : Kyprianou.Ch01.inverseGaussianJumpExponentValue
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T00:37:45.717018+00:00
-- url     : https://prove2.me/theorems/ddaa0f7b-76c6-4317-ae20-dea01034b612
-- title:
--   Inverse-Gaussian Lévy jump integral equals the principal square-root exponent
-- statement:
--   The original inverse-Gaussian Fourier-Lévy integral of 1-exp(i theta x) against its x^(-3/2) exponentially tilted measure equals sqrt(b²-2 i theta)-b with the principal complex square-root branch, without changing the source density.
-- source:
--   Kyprianou (2006), Chapter 1 inverse-Gaussian Lévy exponent and Lévy measure, source-exact child.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Set Complex ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianJumpExponentValue
    (b : ℝ) (hb : 0 < b) :
    let Pi : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-(b ^ 2 * x / 2))))
    ∀ theta : ℝ,
      (∫ x in Set.Ioi (0 : ℝ),
        ((1 : ℂ) -
          Complex.exp (Complex.I * ((theta * x : ℝ) : ℂ))) ∂Pi) =
        Complex.sqrt (((b ^ 2 : ℝ) : ℂ) -
          2 * Complex.I * (theta : ℂ)) - (b : ℂ) := by
  sorry
