-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_curve_bound_pointwise_sections_20261023_22
-- name    : OAI.PiExponent.FormalInterpolation.curve_bound_pointwise_sections_20261023_22
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-23T18:33:06.340787+00:00
-- url     : https://prove2.me/theorems/d5c1f908-eefe-4f52-a535-8351b9706429
-- title:
--   Curve contact yields pointwise bounded sections
-- statement:
--   The geometric core: finite colength and the weighted curve-contact bound yield positive `s` and `D` strictly below the slope budget, and for every nonzero point a section in `I ^ s` with support bounded by `D` whose degree-`D` component does not vanish there. The zero-dimensional case has no nonzero points to detect, but still needs the positive numerical choices. An independent proof route would establish positivity on the weighted blow-up from the curve criterion, then use Serre vanishing to produce bounded sections. This removes the curve-bound-to-sections implication from the parent; that geometric implication remains the main core obligation.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.curve_bound_pointwise_sections_20261023_22
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
