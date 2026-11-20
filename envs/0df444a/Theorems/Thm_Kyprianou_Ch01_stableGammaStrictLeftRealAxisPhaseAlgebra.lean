-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftRealAxisPhaseAlgebra
-- name    : Kyprianou.Ch01.stableGammaStrictLeftRealAxisPhaseAlgebra
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T13:10:31.170354+00:00
-- url     : https://prove2.me/theorems/39c71325-3154-4a2b-a506-c9fb6e0c43a2
-- title:
--   Real positive Mellin rate power expressed in principal complex Gamma phase
-- statement:
--   For u>0 and any real alpha, the real Mellin coefficient (1/u)^(1-alpha)*Gamma(1-alpha) agrees exactly with the principal complex exponential Gamma(1-alpha)*exp((alpha-1)*log u). This is the algebra needed to feed the proved negative-real Mellin integral anchor to the analytic identity theorem.
-- source:
--   Kyprianou Chapter 1 stable Gamma analytic continuation, real positive rates.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Complex Real Set Filter Kyprianou.Ch01
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaStrictLeftRealAxisPhaseAlgebra
    (alpha u : ℝ) (hu : 0 < u) :
    (((((1 / u) ^ (1 - alpha)) * Real.Gamma (1 - alpha) : ℝ)) : ℂ) =
      ((Real.Gamma (1 - alpha) : ℝ) : ℂ) *
        Complex.exp (((alpha - 1 : ℝ) : ℂ) * Complex.log (u : ℂ))
    := by sorry
