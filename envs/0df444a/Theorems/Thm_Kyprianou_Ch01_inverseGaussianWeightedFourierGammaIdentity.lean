-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianWeightedFourierGammaIdentity
-- name    : Kyprianou.Ch01.inverseGaussianWeightedFourierGammaIdentity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T13:01:14.820393+00:00
-- url     : https://prove2.me/theorems/bbdb1873-9241-4e41-89f4-dd9f7ebb555f
-- title:
--   Exact inverse-Gaussian weighted Fourier-Gamma integral on positive real jumps
-- statement:
--   The exact positive-halfline complex Fourier deficit with the original inverse-Gaussian jump density evaluates to the principal complex square-root exponent. This isolates genuine analytic Gamma integration from the Bochner integral change-of-density, with unchanged b>0 and arbitrary real frequency.
-- source:
--   Kyprianou (2006), Chapter 1 inverse Gaussian Lévy exponent, Gamma integral and principal complex square-root.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Set Complex ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianWeightedFourierGammaIdentity
    (b : ℝ) (hb : 0 < b) (theta : ℝ) :
    (∫ x in Set.Ioi (0 : ℝ),
      (ENNReal.ofReal
        ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
          Real.exp (-(b ^ 2 * x / 2)))).toReal •
      ((1 : ℂ) -
        Complex.exp (Complex.I * ((theta * x : ℝ) : ℂ))) ∂volume) =
      Complex.sqrt (((b ^ 2 : ℝ) : ℂ) -
        2 * Complex.I * (theta : ℂ)) - (b : ℂ) := by sorry
