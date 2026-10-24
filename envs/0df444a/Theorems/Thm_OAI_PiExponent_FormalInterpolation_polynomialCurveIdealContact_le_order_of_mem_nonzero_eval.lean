-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurveIdealContact_le_order_of_mem_nonzero_eval
-- name    : OAI.PiExponent.FormalInterpolation.polynomialCurveIdealContact_le_order_of_mem_nonzero_eval
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:56:18.571133+00:00
-- url     : https://prove2.me/theorems/699134fe-93b8-4fa0-ab9d-9d91cbc05c73
-- title:
--   Ideal contact is bounded by any nonzero evaluated member
-- statement:
--   For an affine chart point, the contact of an ideal is at most the order of any member whose evaluation is nonzero. This makes the particular evaluated member an explicit witness in the set defining the contact infimum.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Algebra.MvPolynomial.Eval

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.polynomialCurveIdealContact_le_order_of_mem_nonzero_eval
    {d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (I : Ideal (MvPolynomial (Fin d) Complex))
    (f : MvPolynomial (Fin d) Complex)
    (hchart : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i))
    (hf : f ∈ I)
    (hne : MvPolynomial.aeval x f ≠ 0) :
    (polynomialCurveIdealContact nu x I : Real) ≤
      (polynomialCurveOrder nu (MvPolynomial.aeval x f) : Real) := by sorry
