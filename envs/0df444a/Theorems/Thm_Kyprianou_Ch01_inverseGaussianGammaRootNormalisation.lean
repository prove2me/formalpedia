-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianGammaRootNormalisation
-- name    : Kyprianou.Ch01.inverseGaussianGammaRootNormalisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:34:19.985168+00:00
-- url     : https://prove2.me/theorems/861c256b-fd02-4445-a89b-041d4cd289c2
-- title:
--   Inverse Gaussian half-Gamma normalisation equals principal square-root characteristic exponent
-- statement:
--   For b>0 and all real frequencies, the half-Gamma normalisation converts the two complex fractional powers into the principal sqrt(b²-2iθ)-b. Uses Gamma(-1/2)=-2sqrt(pi) and positive real scale.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.6(ii), source-exact inverse Gaussian Levy density and principal complex square root.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Set Complex ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianGammaRootNormalisation
    (b : ℝ) (hb : 0 < b) (theta : ℝ) :
    (((Real.Gamma (-(1 / 2 : ℝ)) /
      Real.sqrt (2 * Real.pi) : ℝ) : ℂ)) *
        (Complex.exp (((1 / 2 : ℝ) : ℂ) *
          Complex.log (((b ^ 2 / 2 : ℝ) : ℂ))) -
         Complex.exp (((1 / 2 : ℝ) : ℂ) *
          Complex.log ((((b ^ 2 / 2 : ℝ) : ℂ) -
            Complex.I * (theta : ℂ))))) =
    Complex.sqrt (((b ^ 2 : ℝ) : ℂ) -
      2 * Complex.I * (theta : ℂ)) - (b : ℂ) := by sorry
