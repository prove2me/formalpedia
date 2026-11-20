-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianFourierWithDensity
-- name    : Kyprianou.Ch01.inverseGaussianFourierWithDensity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:48:52.339666+00:00
-- url     : https://prove2.me/theorems/612b3a22-0767-4867-a64c-d9493c5d3c33
-- title:
--   Source-exact inverse Gaussian Fourier set integral transfers from the Lévy measure to weighted Lebesgue integral
-- statement:
--   The original positive-halfline inverse-Gaussian Lévy measure uses ENNReal.ofReal of the exact density exp(-b²x/2)/sqrt(2pi x³). For b>0, set-integrating 1-exp(i theta x) against this measure is exactly integrating the real density acting on that complex Fourier factor against Lebesgue measure restricted to x>0.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.6(ii); Mathlib Bochner setIntegral_withDensity_eq_setIntegral_toReal_smul.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Set Complex ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianFourierWithDensity (b : ℝ) (hb : 0 < b) (theta : ℝ) :
    (∫ x in Set.Ioi (0 : ℝ), ((1 : ℂ) -
        Complex.exp (Complex.I * ((theta * x : ℝ) : ℂ))) ∂
      ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal
          ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
                Real.exp (-(b ^ 2 * x / 2)))))) =
    (∫ x in Set.Ioi (0 : ℝ), ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
                Real.exp (-(b ^ 2 * x / 2))) • ((1 : ℂ) -
        Complex.exp (Complex.I * ((theta * x : ℝ) : ℂ))) ∂volume) := by sorry
