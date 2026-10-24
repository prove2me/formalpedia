-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_curve_bound_pointwise_sections_20261023_19
-- name    : OAI.PiExponent.FormalInterpolation.curve_bound_pointwise_sections_20261023_19
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-23T18:27:22.55653+00:00
-- url     : https://prove2.me/theorems/1d1fe775-6662-46ce-a71f-d281996f6c54
-- title:
--   Curve contact yields pointwise bounded sections
-- statement:
--   Given the weighted curve-contact bound, construct positive s and D below the strict slope budget, such that every nonzero point is detected by the degree-D component of some bounded-support polynomial in I^s. This is the geometric core. An independent proof must establish the curve criterion to section-generation step while preserving the strict epsilon allowance; the supplied definition and source summary do not provide that proof.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.curve_bound_pointwise_sections_20261023_19
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∃ s : Nat, 0 < s ∧ ∃ D : Nat,
      (D : Real) < (s : Real) * ((rho : Real) + eps) ∧ 0 < D ∧
      ∀ x : Fin d → Complex,
        (∃ i : Fin d, x i ≠ 0) →
        ∃ g : MvPolynomial (Fin d) Complex,
          g ∈ I ^ s ∧
          (∀ a ∈ g.support,
            ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
          MvPolynomial.eval x
            (MvPolynomial.weightedHomogeneousComponent
              (fun k => (w k : ℚ)) (D : ℚ) g) ≠ 0 := by sorry
