-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_quotient_representatives_monic_relations_with_rounding_margin
-- name    : OAI.PiExponent.FormalInterpolation.weighted_quotient_representatives_monic_relations_with_rounding_margin
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T22:38:25.611407+00:00
-- url     : https://prove2.me/theorems/12efdee6-fa02-42d6-bc07-b65488d066cf
-- title:
--   Representatives with a rounding margin give weighted monic relations
-- statement:
--   Given positive weights and representatives modulo `I^k` bounded by weighted degree `kc`, choose each positive integer exponent just above `kc/wᵢ`. The condition `k(a-c) > wᵢ` ensures its weighted degree is at most `ka`. Subtract the bounded representative of `Xᵢ^{bᵢ}` from that monomial to obtain the required element of `I^k`; the remainder’s support has strictly smaller weighted degree.
-- source:
--   Reduction obligation for OAI.PiExponent.FormalInterpolation.weightedIdealCurveBound_eventual_quotient_representatives (globalInterpolation pillar; weighted compactification / ampleness / Serre vanishing / ordinary Rees recovery argument), split at the interface between the geometric weighted-monic-relations output of the curve criterion and the algebraic weighted division step. (geometric step: curve criterion -> weighted monic relations)

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.weighted_quotient_representatives_monic_relations_with_rounding_margin
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (c a : Rat) (hc : 0 < c) (hca : c < a)
    (k : Nat) (hk : 0 < k)
    (hmargin : ∀ i, (k : Real) * ((a - c : Rat) : Real) > (w i : Real))
    (hrep : ∀ P : MvPolynomial (Fin d) Complex,
      ∃ R : MvPolynomial (Fin d) Complex,
        P - R ∈ I ^ k ∧
        ∀ v ∈ R.support,
          (∑ j, (w j : Real) * (v j : Real)) ≤ (k : Real) * (c : Real)) :
    ∃ k' : Nat, 0 < k' ∧ ∃ (b : Fin d → Nat), (∀ i, 0 < b i) ∧
      ∃ (F : Fin d → MvPolynomial (Fin d) Complex),
        (∀ i, F i ∈ I ^ k') ∧
        (∀ i, ∀ v ∈ (MvPolynomial.X i ^ b i - F i).support,
          (∑ j, (w j : Real) * (v j : Real)) < (w i : Real) * (b i : Real)) ∧
        (∀ i, (w i : Real) * (b i : Real) ≤ (k' : Real) * (a : Real)) := by sorry
