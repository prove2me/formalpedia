-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurve_eval_order_nonneg
-- name    : OAI.PiExponent.FormalInterpolation.polynomialCurve_eval_order_nonneg
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T18:04:40.331603+00:00
-- url     : https://prove2.me/theorems/516ea662-e3dc-49b3-b30a-b0c8e032cb57
-- title:
--   Nonzero chart evaluations have a nonnegative finite order
-- statement:
--   If every coordinate has nonnegative valuation, then a nonzero polynomial evaluation has a finite nonnegative integer valuation, and its order is the corresponding natural number.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Algebra.MvPolynomial.Eval

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.polynomialCurve_eval_order_nonneg
    {d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (f : MvPolynomial (Fin d) Complex)
    (hchart : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i))
    (hne : MvPolynomial.aeval x f ≠ 0) :
    ∃ k : Nat,
      nu.1 (MvPolynomial.aeval x f) = ((k : Int) : WithTop Int) ∧
      polynomialCurveOrder nu (MvPolynomial.aeval x f) = (k : Int) := by sorry
