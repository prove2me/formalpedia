-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurveOrder_support_finite_of_hasPrincipalDivisors
-- name    : OAI.PiExponent.FormalInterpolation.polynomialCurveOrder_support_finite_of_hasPrincipalDivisors
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:59:23.364928+00:00
-- url     : https://prove2.me/theorems/019da36e-8b41-4b2f-96a2-73fd14da4a10
-- title:
--   PolynomialCurvePlace order support is finite given HasPrincipalDivisors
-- statement:
--   Assume $E/\mathbb{C}$ admits principal divisors in the sense of `AlgebraicCurve.HasPrincipalDivisors`: for every nonzero $f\in E$ the function $v\mapsto v.\mathrm{ord}(f)$ on `AlgebraicCurve.Place` places is the evaluation of a finitely supported divisor.
--
--   Then, among the normalized discrete places of type `PolynomialCurvePlace` (integer-valued additive valuations trivial on $\mathbb{C}^\times$ and surjective onto $\mathbb{Z}$), only finitely many $\nu$ satisfy $\mathrm{ord}_\nu(f)\neq 0$.
--
--   This is the comparison between the FormalInterpolation place type and the AlgebraicCurve place type: once principal divisors exist for the latter, the nonzero-order locus for the former is finite. The zero function is assigned order zero at every place by the `untop₀` convention, so its support is empty.
-- source:
--   Bridge lemma for OAI.PiExponent.FormalInterpolation.polynomialCurveOrder_support_finite; compares PolynomialCurvePlace to AlgebraicCurve.Place under HasPrincipalDivisors (cf. AlgebraicCurve.finite_setOf_ord_ne_zero_of_finiteDimensional)

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

open OAI.PiExponent.FormalInterpolation
open AlgebraicCurve

theorem OAI.PiExponent.FormalInterpolation.polynomialCurveOrder_support_finite_of_hasPrincipalDivisors
    {E : Type} [Field E] [Algebra Complex E]
    [HasPrincipalDivisors Complex E] (f : E) :
    Set.Finite {nu : PolynomialCurvePlace E | polynomialCurveOrder nu f ≠ 0} := by sorry
