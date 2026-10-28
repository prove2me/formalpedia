-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCenters_contact_of_pairwise_comaximal
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicCenters_contact_of_pairwise_comaximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T09:12:33.115971+00:00
-- url     : https://prove2.me/theorems/13cb2033-c3b9-4d33-8da2-c20ca8e1f7d2
-- title:
--   Positive contact of a pairwise comaximal product occurs at one factor
-- statement:
--   For any finite pairwise comaximal family of polynomial ideals, positive contact with their product equals the positive contact of one factor. This isolates the valuation and finite-sum argument from the particular logarithmic generators. A proof route is to establish additivity of contact over finite products on the affine branch, show that comaximal ideals cannot both have positive contact there, then use finite-sum arithmetic to select the positive factor; outside that branch, product contact is zero by definition, so the positive premise excludes it.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicCenters_contact_of_pairwise_comaximal
    {K d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (I : Fin K → Ideal (MvPolynomial (Fin d) Complex))
    (hcop : ∀ j k : Fin K, j ≠ k → IsCoprime (I j) (I k))
    (hcontact : 0 < (polynomialCurveIdealContact nu x (∏ j, I j) : Real)) :
    ∃ j : Fin K,
      0 < (polynomialCurveIdealContact nu x (I j) : Real) ∧
      (polynomialCurveIdealContact nu x (I j) : Real) =
        (polynomialCurveIdealContact nu x (∏ j, I j) : Real) := by sorry
