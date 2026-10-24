-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurveIdealContact_finset_product_of_pairwise_eq_or_comaximal
-- name    : OAI.PiExponent.FormalInterpolation.polynomialCurveIdealContact_finset_product_of_pairwise_eq_or_comaximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T18:13:30.133985+00:00
-- url     : https://prove2.me/theorems/13c005e8-77ed-48a5-ae56-1e43dc52a012
-- title:
--   Contact of a finite product of equal-or-comaximal ideals
-- statement:
--   For a finite family of polynomial ideals that are pairwise equal or comaximal, contact of their product is the sum of their contacts, including the empty family.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.polynomialCurveIdealContact_finset_product_of_pairwise_eq_or_comaximal
    {d K : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (S : Finset (Fin K))
    (I : Fin K → Ideal (MvPolynomial (Fin d) Complex))
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      I i = I j ∨ I i ⊔ I j = ⊤) :
    polynomialCurveIdealContact nu x (∏ j ∈ S, I j) =
      ∑ j ∈ S, polynomialCurveIdealContact nu x (I j) := by sorry
