-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurve_principal_divisor_balance_finite_parameter_degree
-- name    : OAI.PiExponent.FormalInterpolation.polynomialCurve_principal_divisor_balance_finite_parameter_degree
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T09:13:39.668173+00:00
-- url     : https://prove2.me/theorems/42c3f00b-e5de-4b36-8aec-ecd012309d7e
-- title:
--   Positive and negative order totals in a finite parameter extension
-- statement:
--   For a finite extension of ℂ(t), the sum of positive orders equals the sum of pole orders. This supplies the degree equality in the parameter case and removes that entire conjunct from the parent proof. A proof route is to identify the normalized places with closed points of the smooth projective curve of E/ℂ and apply the degree-zero theorem for the principal divisor of f; the algebraically closed constant field makes the residue degrees one. The f = 0 case has both sums zero. This is the main remaining mathematical obligation, and the route still requires formalizing the place classification and principal-divisor theorem.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IsAlgClosed.Basic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.polynomialCurve_principal_divisor_balance_finite_parameter_degree
    (E : Type) [Field E] [Algebra Complex E]
    (t : E)
    (hfinite : FiniteDimensional (IntermediateField.adjoin Complex {t}) E)
    (ht : Transcendental Complex t) (f : E) :
    (∑ᶠ nu : PolynomialCurvePlace E,
      max 0 (polynomialCurveOrder nu f : Real)) =
    (∑ᶠ nu : PolynomialCurvePlace E,
      max 0 (-(polynomialCurveOrder nu f : Real))) := by sorry
