-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurve_principal_divisor_balance
-- name    : OAI.PiExponent.FormalInterpolation.polynomialCurve_principal_divisor_balance
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T08:54:25.354994+00:00
-- url     : https://prove2.me/theorems/b9c5c901-023b-4f95-bfc3-049b564a30b6
-- title:
--   Finite support and zero–pole balance for normalized curve places
-- statement:
--   If the field is finite over every transcendental one-element parameter field, each function has finitely supported normalized orders, and its total positive and negative orders agree. The zero function is included using the defined zero-order convention.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IsAlgClosed.Basic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.polynomialCurve_principal_divisor_balance
    (E : Type) [Field E] [Algebra Complex E]
    (hfinite : ∀ g : E, Transcendental Complex g →
      FiniteDimensional (IntermediateField.adjoin Complex {g}) E)
    (f : E) :
    (fun nu : PolynomialCurvePlace E =>
      (polynomialCurveOrder nu f : Real)).HasFiniteSupport ∧
    (∑ᶠ nu : PolynomialCurvePlace E,
      max 0 (polynomialCurveOrder nu f : Real)) =
    (∑ᶠ nu : PolynomialCurvePlace E,
      max 0 (-(polynomialCurveOrder nu f : Real))) := by sorry
