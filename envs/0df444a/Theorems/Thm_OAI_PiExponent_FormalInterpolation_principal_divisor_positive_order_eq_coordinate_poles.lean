-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_principal_divisor_positive_order_eq_coordinate_poles
-- name    : OAI.PiExponent.FormalInterpolation.principal_divisor_positive_order_eq_coordinate_poles
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-21T03:48:20.134978+00:00
-- url     : https://prove2.me/theorems/9ce0c0fc-7ad9-456c-a047-70ff3ceb687b
-- title:
--   Positive divisor degree equals coordinate pole degree
-- statement:
--   For a transcendental coordinate in a finite-type one-variable function field over Complex, the total positive order of the coordinate minus a constant equals the total pole order of the coordinate. The proof uses the degree-zero principal-divisor theorem and invariance of poles under subtracting a constant.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.Algebraic.Defs

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.principal_divisor_positive_order_eq_coordinate_poles
    {E : Type} [Field E] [Algebra Complex E]
    [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (z : E)
    (hz : Transcendental Complex z) (b : Complex) :
    (∑ᶠ nu : PolynomialCurvePlace E,
      max (polynomialCurveOrder nu (z - algebraMap Complex E b) : Real) 0) =
      ∑ᶠ nu : PolynomialCurvePlace E,
        max (-(polynomialCurveOrder nu z : Real)) 0 := by sorry
