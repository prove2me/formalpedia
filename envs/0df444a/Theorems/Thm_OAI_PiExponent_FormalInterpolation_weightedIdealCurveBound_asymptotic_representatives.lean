-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weightedIdealCurveBound_asymptotic_representatives
-- name    : OAI.PiExponent.FormalInterpolation.weightedIdealCurveBound_asymptotic_representatives
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-20T18:25:00.343006+00:00
-- url     : https://prove2.me/theorems/acc431b2-4677-460d-817c-cea3f056e3f9
-- title:
--   Asymptotic weighted representatives from curve contact
-- statement:
--   For every positive real slack eps, there is a fixed additive constant C such that every polynomial has a representative modulo I^n whose weighted support degrees are at most n times rho + eps, plus C, uniformly for all n.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.weightedIdealCurveBound_asymptotic_representatives
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∃ C : Nat, ∀ n : Nat, ∀ p : MvPolynomial (Fin d) Complex,
        ∃ q : MvPolynomial (Fin d) Complex,
          p - q ∈ I ^ n ∧
          ∀ a ∈ q.support,
            ∑ i, (w i : Real) * (a i : Real) ≤
              (n : Real) * ((rho : Real) + eps) + (C : Real) := by sorry
