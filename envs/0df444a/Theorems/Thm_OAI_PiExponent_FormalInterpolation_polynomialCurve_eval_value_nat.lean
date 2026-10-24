-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurve_eval_value_nat
-- name    : OAI.PiExponent.FormalInterpolation.polynomialCurve_eval_value_nat
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T18:08:33.84556+00:00
-- url     : https://prove2.me/theorems/a68cf0d1-bc3e-46d9-a90b-bb3c2495baec
-- title:
--   Polynomial evaluation has a finite natural valuation
-- statement:
--   Under the coordinate nonnegativity condition, every nonzero polynomial evaluation has valuation equal to a natural number embedded into `WithTop Int`. The chart hypothesis bounds evaluated monomials and their finite sum; nonzeroness excludes the infinite value `⊤`.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Algebra.MvPolynomial.Eval

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.polynomialCurve_eval_value_nat
    {d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (f : MvPolynomial (Fin d) Complex)
    (hchart : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i))
    (hne : MvPolynomial.aeval x f ≠ 0) :
    ∃ k : Nat, nu.1 (MvPolynomial.aeval x f) = ((k : Int) : WithTop Int) := by sorry
