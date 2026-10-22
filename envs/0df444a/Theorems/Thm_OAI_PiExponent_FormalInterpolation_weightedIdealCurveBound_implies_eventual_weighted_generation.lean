-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weightedIdealCurveBound_implies_eventual_weighted_generation
-- name    : OAI.PiExponent.FormalInterpolation.weightedIdealCurveBound_implies_eventual_weighted_generation
-- status  : Open
-- author  : @Ethan Cheung
-- created : 2026-10-21T07:08:54.878264+00:00
-- url     : https://prove2.me/theorems/d81695f5-3da7-439d-8cdc-d9c87e919fcf
-- title:
--   Curve bound implies eventual generation by subcritical weighted sections
-- statement:
--   Under a WeightedIdealCurveBound of slope rho, for every positive eps the quotient map from the subtype of polynomials of weighted degree at most n(rho+eps) onto the quotient by I^n is surjective for all sufficiently large n. This is the geometric generation step (eps-ample Rees twist and Serre vanishing) underlying eventual weighted representatives.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.weightedIdealCurveBound_implies_eventual_weighted_generation
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      Function.Surjective
        (fun q : {q : MvPolynomial (Fin d) Complex //
              ∀ a ∈ q.support,
                ∑ i, (w i : Real) * (a i : Real) ≤
                  (n : Real) * ((rho : Real) + eps)} =>
          Ideal.Quotient.mk (I ^ n) q.1) := by sorry
