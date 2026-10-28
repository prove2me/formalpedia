-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_top_ideal_has_coordinate_relation
-- name    : OAI.PiExponent.FormalInterpolation.top_ideal_has_coordinate_relation
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-25T00:25:16.35284+00:00
-- url     : https://prove2.me/theorems/abcf464f-1d46-4236-9cee-fd1ba2fcac97
-- title:
--   The unit ideal satisfies the coordinate conclusion
-- statement:
--   For I = ⊤, take n = 1, f = 0, and q = w_i. The support condition is vacuous and every polynomial difference belongs to I^s. Since rho ≥ 0 and eps > 0, choose a positive integer s large enough that w_i < s * (rho + eps). This covers the unit-ideal boundary case, including rho = 0.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.top_ideal_has_coordinate_relation
    (d : Nat) (I : Ideal (MvPolynomial (Fin d) Complex)) (hI : I = ⊤)
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (eps : Real) (heps : 0 < eps) (i : Fin d) :
    ∃ s : Nat, 0 < s ∧
      ∃ q : Rat, 0 < q ∧ (q : Real) < (s : Real) * ((rho : Real) + eps) ∧
        ∃ n : Nat, 0 < n ∧ (n : Rat) * w i = q ∧
          ∃ f : MvPolynomial (Fin d) Complex,
            MvPolynomial.X i ^ n - f ∈ I ^ s ∧
            ∀ a, a ∈ f.support →
              ∑ j, (w j : Real) * (a j : Real) < (q : Real) := by sorry
