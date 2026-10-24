-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurveContact_pos_eval
-- name    : OAI.PiExponent.FormalInterpolation.polynomialCurveContact_pos_eval
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:58:57.961226+00:00
-- url     : https://prove2.me/theorems/ed9f48bb-040d-449f-a201-4bd165669797
-- title:
--   Positive ideal contact forces positive value of every ideal element
-- statement:
--   If an affine ideal has positive contact at a polynomial-curve place, every member of that ideal evaluates to an element of strictly positive place value.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.polynomialCurveContact_pos_eval
    {d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (I : Ideal (MvPolynomial (Fin d) Complex))
    (hcontact : 0 < polynomialCurveIdealContact nu x I)
    (f : MvPolynomial (Fin d) Complex) (hf : f ∈ I) :
    (0 : WithTop Int) < nu.1 (MvPolynomial.aeval x f) := by sorry
