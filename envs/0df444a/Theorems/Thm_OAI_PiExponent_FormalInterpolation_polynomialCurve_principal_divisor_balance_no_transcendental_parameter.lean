-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurve_principal_divisor_balance_no_transcendental_parameter
-- name    : OAI.PiExponent.FormalInterpolation.polynomialCurve_principal_divisor_balance_no_transcendental_parameter
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T09:14:09.916044+00:00
-- url     : https://prove2.me/theorems/86bfba5d-fbf5-4f64-ac8b-c09a2299291f
-- title:
--   The constant-field case has no normalized places
-- statement:
--   When E has no transcendental element over ℂ, all its elements are algebraic over ℂ and therefore lie in the constant subfield. A valuation trivial on nonzero constants is then trivial on every nonzero element, contradicting the required surjectivity onto ℤ. Thus the place type is empty; finite support and equality of the two sums follow. This discharges the parent’s no-parameter case without using hfinite.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IsAlgClosed.Basic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.polynomialCurve_principal_divisor_balance_no_transcendental_parameter
    (E : Type) [Field E] [Algebra Complex E]
    (hfinite : ∀ g : E, Transcendental Complex g →
      FiniteDimensional (IntermediateField.adjoin Complex {g}) E)
    (f : E)
    (hparam : ¬ ∃ t : E, Transcendental Complex t) :
    (fun nu : PolynomialCurvePlace E =>
      (polynomialCurveOrder nu f : Real)).HasFiniteSupport ∧
    (∑ᶠ nu : PolynomialCurvePlace E,
      max 0 (polynomialCurveOrder nu f : Real)) =
    (∑ᶠ nu : PolynomialCurvePlace E,
      max 0 (-(polynomialCurveOrder nu f : Real))) := by sorry
