-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomial_curve_zero_divisor_bound
-- name    : OAI.PiExponent.FormalInterpolation.polynomial_curve_zero_divisor_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-21T04:15:55.682592+00:00
-- url     : https://prove2.me/theorems/15b13aef-61db-46b5-89f1-21b68c879b36
-- title:
--   Weighted height bounds the positive zero divisor on a curve
-- statement:
--   For a nonzero polynomial evaluation on a generating one-variable function field, the places where its order is positive form a finite set, and its total positive order is at most the polynomial’s weighted support height times the total weighted coordinate pole degree.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.polynomial_curve_zero_divisor_bound
    {d : Nat} (E : Type) [Field E] [Algebra Complex E]
    [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin d → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (N : Real) (hN : 0 ≤ N)
    (F : MvPolynomial (Fin d) Complex)
    (hF : logarithmicDegreeBound w N F)
    (hne : MvPolynomial.aeval x F ≠ 0) :
    ({nu : PolynomialCurvePlace E |
      0 < polynomialCurveOrder nu (MvPolynomial.aeval x F)}.Finite ∧
      (∑ᶠ nu : PolynomialCurvePlace E,
        max (polynomialCurveOrder nu (MvPolynomial.aeval x F) : Real) 0) ≤
        N * (∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x w)) := by sorry
