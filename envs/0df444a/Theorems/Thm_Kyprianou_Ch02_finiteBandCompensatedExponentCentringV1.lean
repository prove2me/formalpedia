-- Prove2me | Theorems.Thm_Kyprianou_Ch02_finiteBandCompensatedExponentCentringV1
-- name    : Kyprianou.Ch02.finiteBandCompensatedExponentCentringV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T22:25:39.984809+00:00
-- url     : https://prove2.me/theorems/07efe348-a310-4c1f-9a92-7acd9e72828a
-- title:
--   Compensated finite-band exponent: exact cancellation of the linear compensator
-- statement:
--   On a finite band strictly inside the unit cutoff, the compensated integrand is the raw exponent integrand minus the linear term. Integrability follows from the proved full compensated-integrand integrability and boundedness of the linear term on the finite band. Linearity and exp_add yield the cancellation identity.
-- source:
--   Kyprianou (2006), Theorem 2.1, compensated finite Poisson bands; exact reduction of sourceFaithfulCompensatedBandCharFunKLSV1.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.finiteBandCompensatedExponentCentringV1
    (levyMeasure : Measure ℝ)
    (hlevyMeasure : IsLevyMeasure levyMeasure)
    (e : ℝ) (he : 0 < e) (he1 : e < 1)
    (t : ℝ≥0) (ξ : ℝ) :
    Complex.exp ((((t : ℝ) : ℂ)) *
      ∫ x in {x : ℝ | e ≤ |x| ∧ |x| < 1},
        (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂levyMeasure) *
      Complex.exp ((-(((t : ℝ) : ℂ))) *
        ((∫ x in {x : ℝ | e ≤ |x| ∧ |x| < 1}, x ∂levyMeasure : ℝ) : ℂ) *
        (ξ : ℂ) * Complex.I) =
    Complex.exp ((((t : ℝ) : ℂ)) *
      ∫ x in {x : ℝ | e ≤ |x| ∧ |x| < 1},
        ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure) := by sorry
