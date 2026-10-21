-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomial_curve_mass_le_zero_divisor
-- name    : OAI.PiExponent.FormalInterpolation.polynomial_curve_mass_le_zero_divisor
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-21T04:16:10.620715+00:00
-- url     : https://prove2.me/theorems/9601c0d6-8142-4974-ae7a-28a318d18ca1
-- title:
--   Local scaled mass is bounded by the positive zero divisor
-- statement:
--   For nonnegative mass on curve places, if each positive mass is locally bounded by r times the function’s order, then the total scaled mass is bounded by r times the total positive order, provided the positive-order support is finite.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.polynomial_curve_mass_le_zero_divisor
    {E : Type} [Field E] [Algebra Complex E]
    (f : E) (a r : Real) (ha : 0 < a) (hr : 0 < r)
    (b : PolynomialCurvePlace E → Real) (hb : ∀ nu, 0 ≤ b nu)
    (hlocal : ∀ nu, 0 < b nu →
      a * b nu ≤ r * (polynomialCurveOrder nu f : Real))
    (hpositiveFinite :
      {nu : PolynomialCurvePlace E | 0 < polynomialCurveOrder nu f}.Finite) :
    a * (∑ᶠ nu : PolynomialCurvePlace E, b nu) ≤
      r * (∑ᶠ nu : PolynomialCurvePlace E,
        max (polynomialCurveOrder nu f : Real) 0) := by sorry
