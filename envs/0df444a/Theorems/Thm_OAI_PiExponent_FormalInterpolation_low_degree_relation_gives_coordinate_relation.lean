-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_low_degree_relation_gives_coordinate_relation
-- name    : OAI.PiExponent.FormalInterpolation.low_degree_relation_gives_coordinate_relation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T00:24:38.765326+00:00
-- url     : https://prove2.me/theorems/e708e7a6-dc40-4e39-b568-ed9411c62b98
-- title:
--   A bounded low-degree relation gives the required coordinate witness
-- statement:
--   Convert a bounded low-degree relation into the target by setting s = 1, q = (n : Rat) * w_i, n' = n, and g = f. The hypotheses give q > 0, q ≤ rho, and therefore q < rho + eps; ideal membership uses I^1 = I. The strict support bound becomes the required bound because q is the real cast of n times w_i.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.low_degree_relation_gives_coordinate_relation
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (eps : Real) (heps : 0 < eps) (i : Fin d)
    (n : Nat) (hn : 0 < n) (f : MvPolynomial (Fin d) Complex)
    (hrel : MvPolynomial.X i ^ n - f ∈ I)
    (hsupport : ∀ a, a ∈ f.support →
      ∑ j, (w j : Real) * (a j : Real) < (n : Real) * (w i : Real))
    (hbound : (n : Real) * (w i : Real) ≤ (rho : Real)) :
    ∃ s : Nat, 0 < s ∧
      ∃ q : Rat, 0 < q ∧ (q : Real) < (s : Real) * ((rho : Real) + eps) ∧
        ∃ n' : Nat, 0 < n' ∧ (n' : Rat) * w i = q ∧
          ∃ g : MvPolynomial (Fin d) Complex,
            MvPolynomial.X i ^ n' - g ∈ I ^ s ∧
            ∀ a, a ∈ g.support →
              ∑ j, (w j : Real) * (a j : Real) < (q : Real) := by sorry
