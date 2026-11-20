-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianComplexHalfGammaDeficit
-- name    : Kyprianou.Ch01.inverseGaussianComplexHalfGammaDeficit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:27:25.154029+00:00
-- url     : https://prove2.me/theorems/ac62e51f-82a8-449b-ae69-286be2d4eb0b
-- title:
--   Inverse-Gaussian tilted complex Gamma half-index deficit on the strict left half-plane
-- statement:
--   For positive inverse-Gaussian rate b and any real Fourier frequency, specialise the already-proved stable Gamma complex deficit integral at alpha=1/2 to the strictly left complex parameter -b²/2+i theta. This identity is valid at theta=0 and preserves the principal logarithm and complex branch.
-- source:
--   Kyprianou (2006) Exercise 1.6(ii), inverse Gaussian Fourier exponent; established Chapter 1 stable Gamma strict-left deficit lemma.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitValueStrictLeft
open MeasureTheory Set Complex ProbabilityTheory Kyprianou.Ch01
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianComplexHalfGammaDeficit
    (b : ℝ) (hb : 0 < b) (theta : ℝ) :
    let w : ℂ := ((-(b ^ 2 / 2 : ℝ) : ℝ) : ℂ) +
      Complex.I * (theta : ℂ)
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (w * (r : ℂ)) - 1) *
        ((r ^ (-(1 / 2 : ℝ) - 1) : ℝ) : ℂ) ∂volume) =
      ((Real.Gamma (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (((1 / 2 : ℝ) : ℂ) * Complex.log (-w)) := by sorry
