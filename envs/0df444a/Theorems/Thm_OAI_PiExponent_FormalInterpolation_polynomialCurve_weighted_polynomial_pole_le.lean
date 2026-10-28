-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurve_weighted_polynomial_pole_le
-- name    : OAI.PiExponent.FormalInterpolation.polynomialCurve_weighted_polynomial_pole_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T08:54:37.434929+00:00
-- url     : https://prove2.me/theorems/633f6da7-d471-45a6-89c1-0dd4682b5764
-- title:
--   Weighted polynomial support bounds the pole at each place
-- statement:
--   At any normalized place, a polynomial satisfying the closed weighted support cutoff has evaluated pole order at most N times the coordinate pole allowance. All weights are strictly positive; zero evaluation, no variables, and N = 0 are included.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.polynomialCurve_weighted_polynomial_pole_le
    {d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E)
    (x : Fin d → E) (w : Fin d → Rat)
    (hw : ∀ i, 0 < (w i : Real))
    (N : Nat) (P : MvPolynomial (Fin d) Complex)
    (hP : fibreContactSupportBound w N P) :
    max 0 (-(polynomialCurveOrder nu (MvPolynomial.aeval x P) : Real)) ≤
      (N : Real) * polynomialCurvePole nu x w := by sorry
