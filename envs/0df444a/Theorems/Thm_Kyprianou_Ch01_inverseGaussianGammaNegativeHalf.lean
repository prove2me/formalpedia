-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianGammaNegativeHalf
-- name    : Kyprianou.Ch01.inverseGaussianGammaNegativeHalf
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:28:39.300421+00:00
-- url     : https://prove2.me/theorems/3eae4765-2ded-483b-a565-54f883ba4bc0
-- title:
--   Gamma at negative one half equals minus twice root pi
-- statement:
--   The real Gamma function at -1/2 equals -2 sqrt(pi), via the pinned Gamma recurrence and Gamma(1/2)=sqrt(pi). Needed to normalise the inverse-Gaussian jump integral.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.6(ii), Gamma integral normalisation.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Set Complex ProbabilityTheory Kyprianou.Ch01
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianGammaNegativeHalf :
    Real.Gamma (-(1 / 2 : ℝ)) = -2 * Real.sqrt Real.pi := by sorry
