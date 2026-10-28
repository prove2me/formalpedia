-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurveOrder_principal_divisor_data
-- name    : OAI.PiExponent.FormalInterpolation.polynomialCurveOrder_principal_divisor_data
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T09:19:45.385014+00:00
-- url     : https://prove2.me/theorems/7afab19a-d336-47b7-97f4-7ae8902e577c
-- title:
--   Finite support and degree zero for principal divisors on a finite parameter field
-- statement:
--   For a finite extension of `ℂ(t)`, the normalized places where a function has nonzero order form a finite set, and the sum of its orders is zero. This packages the principal-divisor degree-zero theorem in the valuation interface used by the target. For zero, both conclusions hold directly; for nonzero functions, a proof must identify the defined normalized valuations with closed points of the smooth projective curve and use residue degree one over `ℂ`.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IsAlgClosed.Basic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.polynomialCurveOrder_principal_divisor_data
    (E : Type) [Field E] [Algebra Complex E]
    (t : E)
    (hfinite : FiniteDimensional (IntermediateField.adjoin Complex {t}) E)
    (ht : Transcendental Complex t) (f : E) :
    (Set.Finite {nu : PolynomialCurvePlace E |
      polynomialCurveOrder nu f ≠ 0}) ∧
      (∑ᶠ nu : PolynomialCurvePlace E,
        (polynomialCurveOrder nu f : Real)) = 0 := by
  sorry
