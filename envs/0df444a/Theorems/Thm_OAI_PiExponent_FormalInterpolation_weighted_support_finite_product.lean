-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_support_finite_product
-- name    : OAI.PiExponent.FormalInterpolation.weighted_support_finite_product
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T18:15:37.738301+00:00
-- url     : https://prove2.me/theorems/64048262-7cc3-42a9-8789-9371a257bbdc
-- title:
--   Weight bounds add across finite polynomial products
-- statement:
--   For any finite family of multivariate polynomials, if every supported exponent in each factor has weighted sum at most that factor's bound, then every supported exponent in the product has weighted sum at most the sum of the bounds. No sign condition on the weights or bounds is required.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.weighted_support_finite_product
    {d : Nat} {ι : Type} [Fintype ι] [DecidableEq ι]
    (w : Fin d → Rat)
    (f : ι → MvPolynomial (Fin d) Complex) (B : ι → Real)
    (hweight : ∀ i, ∀ a ∈ (f i).support,
      ∑ l, (w l : Real) * (a l : Real) ≤ B i) :
    ∀ a ∈ (∏ i : ι, f i).support,
      ∑ l, (w l : Real) * (a l : Real) ≤ ∑ i, B i := by sorry
