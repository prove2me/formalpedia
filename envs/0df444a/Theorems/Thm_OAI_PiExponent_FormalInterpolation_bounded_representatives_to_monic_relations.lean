-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_representatives_to_monic_relations
-- name    : OAI.PiExponent.FormalInterpolation.bounded_representatives_to_monic_relations
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T23:00:54.817332+00:00
-- url     : https://prove2.me/theorems/29725b24-53f0-4727-afc6-cbf6a048df8c
-- title:
--   Bounded representatives yield a family of monic relations
-- statement:
--   For a family of exponents whose weighted degrees strictly exceed `k c`, bounded representatives modulo `I^k` give a family of ideal elements with the required strict support bounds.
-- source:
--   Reduction obligation for OAI.PiExponent.FormalInterpolation.weightedIdealCurveBound_eventual_quotient_representatives (globalInterpolation pillar; weighted compactification / ampleness / Serre vanishing / ordinary Rees recovery argument), split at the interface between the geometric weighted-monic-relations output of the curve criterion and the algebraic weighted division step. (geometric step: curve criterion -> weighted monic relations)

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.bounded_representatives_to_monic_relations
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (c : Rat) (k : Nat)
    (hrep : ∀ P : MvPolynomial (Fin d) Complex,
      ∃ R : MvPolynomial (Fin d) Complex,
        P - R ∈ I ^ k ∧
        ∀ v ∈ R.support,
          (∑ j, (w j : Real) * (v j : Real)) ≤ (k : Real) * (c : Real))
    (b : Fin d → Nat)
    (hlower : ∀ i, (k : Real) * (c : Real) < (w i : Real) * (b i : Real)) :
    ∃ F : Fin d → MvPolynomial (Fin d) Complex,
      (∀ i, F i ∈ I ^ k) ∧
      (∀ i, ∀ v ∈ (MvPolynomial.X i ^ b i - F i).support,
        (∑ j, (w j : Real) * (v j : Real)) < (w i : Real) * (b i : Real)) := by sorry
