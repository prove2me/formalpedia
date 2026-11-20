-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianFourierWeightedIntegral
-- name    : Kyprianou.Ch01.inverseGaussianFourierWeightedIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:50:33.431107+00:00
-- url     : https://prove2.me/theorems/fdc0af8d-5fd9-4842-b28a-6e37fd7da96f
-- title:
--   Convert the original inverse Gaussian Fourier Levy measure to weighted Gamma exponential difference
-- statement:
--   The original Fourier-Lévy integral against the exact inverse Gaussian measure equals the fixed normalising constant times a half-index Gamma exponential-difference integral, preserving original positive support and principal branch.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.6(ii) original inverse Gaussian jump exponent.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Set Complex ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianFourierWeightedIntegral
    (b : ℝ) (hb : 0 < b) :
    let Pi : Measure ℝ := (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-(b ^ 2 * x / 2))))
    ∀ theta : ℝ,
      (∫ x in Set.Ioi (0 : ℝ), ((1 : ℂ) -
          Complex.exp (Complex.I * ((theta * x : ℝ) : ℂ))) ∂Pi) =
      (((1 / Real.sqrt (2 * Real.pi) : ℝ)) : ℂ) * (∫ r in Set.Ioi (0 : ℝ),
        (Complex.exp (((-(b ^ 2 / 2) : ℝ) : ℂ) * (r : ℂ)) - Complex.exp ((((-(b ^ 2 / 2) : ℝ) : ℂ) +
            Complex.I * (theta : ℂ)) * (r : ℂ))) *
          ((r ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) ∂volume) := by sorry
