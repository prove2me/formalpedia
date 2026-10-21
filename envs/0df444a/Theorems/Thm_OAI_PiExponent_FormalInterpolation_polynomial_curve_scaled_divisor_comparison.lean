-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomial_curve_scaled_divisor_comparison
-- name    : OAI.PiExponent.FormalInterpolation.polynomial_curve_scaled_divisor_comparison
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-21T03:42:12.108994+00:00
-- url     : https://prove2.me/theorems/d9159ae5-aa1b-492b-91a1-9c6162370939
-- title:
--   Scaled zero-divisor comparison against weighted coordinate poles
-- statement:
--   For a nonzero polynomial evaluation on a generating one-variable complex function field, any nonnegative branch mass bounded by its scaled positive orders has total mass bounded by the polynomial's weighted height times the weighted coordinate pole degree.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.polynomial_curve_scaled_divisor_comparison
    {d : Nat} (E : Type) [Field E] [Algebra Complex E]
    [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin d → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (N : Real) (hN : 0 ≤ N)
    (F : MvPolynomial (Fin d) Complex)
    (hF : logarithmicDegreeBound w N F)
    (hne : MvPolynomial.aeval x F ≠ 0)
    (a r : Real) (ha : 0 < a) (hr : 0 < r)
    (b : PolynomialCurvePlace E → Real) (hb : ∀ nu, 0 ≤ b nu)
    (hlocal : ∀ nu, 0 < b nu →
      a * b nu ≤ r * (polynomialCurveOrder nu (MvPolynomial.aeval x F) : Real)) :
    a * (∑ᶠ nu : PolynomialCurvePlace E, b nu) ≤
      r * N * (∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x w) := by sorry
