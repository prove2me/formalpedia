-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_rationalAdjoin_principal_divisor
-- name    : OAI.PiExponent.FormalInterpolation.rationalAdjoin_principal_divisor
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T09:29:16.255051+00:00
-- url     : https://prove2.me/theorems/d6fc3176-1595-461c-81fb-bc5f69b8eede
-- title:
--   Degree zero for a rational function field
-- statement:
--   In the field C(t), the normalized orders of any rational function sum to zero. Since C is algebraically closed, every irreducible polynomial in C[t] is linear; factoring a numerator and denominator therefore identifies finite places with their roots, while the remaining place is infinity. The finite orders sum to numerator degree minus denominator degree, and the order at infinity is the opposite. For g = 0 every order is zero by definition.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IsAlgClosed.Basic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.rationalAdjoin_principal_divisor
    (E : Type) [Field E] [Algebra Complex E]
    (t : E) (ht : Transcendental Complex t)
    (g : IntermediateField.adjoin Complex {t}) :
    (∑ᶠ nu : PolynomialCurvePlace (IntermediateField.adjoin Complex {t}),
      (polynomialCurveOrder nu g : Real)) = 0 := by
  sorry
