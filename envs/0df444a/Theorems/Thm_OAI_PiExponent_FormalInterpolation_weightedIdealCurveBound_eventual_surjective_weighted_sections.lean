-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weightedIdealCurveBound_eventual_surjective_weighted_sections
-- name    : OAI.PiExponent.FormalInterpolation.weightedIdealCurveBound_eventual_surjective_weighted_sections
-- status  : Open
-- author  : @Ethan Cheung
-- created : 2026-10-21T07:03:11.192275+00:00
-- url     : https://prove2.me/theorems/d5c27072-6718-4b7d-8007-0096bf7dfd4f
-- title:
--   Eventual surjectivity of subcritical weighted sections onto ideal powers
-- statement:
--   Under a WeightedIdealCurveBound of slope rho, for every eps>0 the polynomials of weighted degree at most n(rho+eps) eventually surject onto the quotient by I^n (no additive constant).
-- source:
--   https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Ampleness (curve-contact Nakai criterion implies eventual generation of weighted Rees sections)

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.weightedIdealCurveBound_eventual_surjective_weighted_sections
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      ∀ p : MvPolynomial (Fin d) Complex,
        ∃ q : MvPolynomial (Fin d) Complex,
          p - q ∈ I ^ n ∧
          ∀ a ∈ q.support,
            ∑ i, (w i : Real) * (a i : Real) ≤
              (n : Real) * ((rho : Real) + eps) := by sorry
