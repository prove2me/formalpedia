-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianJumpGammaDifference
-- name    : Kyprianou.Ch01.inverseGaussianJumpGammaDifference
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:34:19.914945+00:00
-- url     : https://prove2.me/theorems/2e6cb407-e02c-47e7-961b-899c24f3964f
-- title:
--   Inverse Gaussian original Fourier-Lévy integral as complex Gamma half-index difference
-- statement:
--   Exact source density with factor exp(-b²x/2)/sqrt(2pi x³), without changes to support, equals the difference of the two left-half-plane Gamma fractional powers multiplied by Gamma(-1/2)/sqrt(2pi).
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.6(ii), source-exact inverse Gaussian Levy density and principal complex square root.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Set Complex ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianJumpGammaDifference
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
      (((Real.Gamma (-(1 / 2 : ℝ)) /
        Real.sqrt (2 * Real.pi) : ℝ) : ℂ)) *
        (Complex.exp (((1 / 2 : ℝ) : ℂ) *
          Complex.log (((b ^ 2 / 2 : ℝ) : ℂ))) -
         Complex.exp (((1 / 2 : ℝ) : ℂ) *
          Complex.log ((((b ^ 2 / 2 : ℝ) : ℂ) -
            Complex.I * (theta : ℂ))))) := by sorry
