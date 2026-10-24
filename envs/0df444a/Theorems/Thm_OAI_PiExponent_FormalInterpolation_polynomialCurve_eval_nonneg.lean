-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurve_eval_nonneg
-- name    : OAI.PiExponent.FormalInterpolation.polynomialCurve_eval_nonneg
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T18:11:41.207528+00:00
-- url     : https://prove2.me/theorems/12a3147e-928e-45d8-9671-3b97f99e4931
-- title:
--   Polynomial evaluation has nonnegative valuation on the affine chart
-- statement:
--   If every coordinate lies in the nonnegative chart of the place, every multivariate polynomial evaluation has nonnegative valuation, including when the evaluation is zero (whose value is top).
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Algebra.MvPolynomial.Eval

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.polynomialCurve_eval_nonneg
    {d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (f : MvPolynomial (Fin d) Complex)
    (hchart : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i)) :
    0 ≤ nu.1 (MvPolynomial.aeval x f) := by sorry
