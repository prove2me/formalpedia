-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurveOrder_support_finite
-- name    : OAI.PiExponent.FormalInterpolation.polynomialCurveOrder_support_finite
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:41:27.691803+00:00
-- url     : https://prove2.me/theorems/0dad6d79-5b69-45fb-ac0b-151c7182712b
-- title:
--   Nonzero orders of a function occur at only finitely many normalized places
-- statement:
--   Let $E/\mathbb{C}$ be a finitely generated field extension of transcendence degree one, and let $f\in E$. Among the normalized discrete places of $E$ that are trivial on $\mathbb{C}^\times$ (the type `PolynomialCurvePlace`), only finitely many places $\nu$ satisfy $\operatorname{ord}_\nu(f)\neq 0$.
--
--   This is the standard finiteness of support for a principal divisor on a smooth projective model of a one-variable function field over an algebraically closed constant field. The zero function is assigned order zero at every place by the `untop₀` convention, so its support is empty.
-- source:
--   Standard fact for algebraic function fields of one variable (product formula / principal divisors have finite support). Used as the geometric core of OAI.PiExponent.FormalInterpolation.coordinateWeightedPole_support_finite on Prove2Me; cf. OpenAI PiExponent Geometry/CurveZeroPole and Dedekind HeightOneSpectrum.Support.finite in Mathlib.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.Algebraic.Defs

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.polynomialCurveOrder_support_finite
    {E : Type} [Field E] [Algebra Complex E]
    [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (f : E) :
    Set.Finite {nu : PolynomialCurvePlace E | polynomialCurveOrder nu f ≠ 0} := by sorry
