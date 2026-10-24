-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_curve_bound_bounded_power_system
-- name    : OAI.PiExponent.FormalInterpolation.curve_bound_bounded_power_system
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-23T08:42:55.114783+00:00
-- url     : https://prove2.me/theorems/ad07d61a-36d8-43a7-8c61-8455336fb8e7
-- title:
--   Curve contact produces a bounded ordinary-power system
-- statement:
--   For every positive slack, curve contact yields elements in a positive ordinary power of the ideal, with support bounded by a strictly subcritical weighted degree. Their degree-D weighted homogeneous components generate an ideal containing a positive power of every coordinate.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.curve_bound_bounded_power_system
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∃ s : Nat, 0 < s ∧ ∃ D : Nat,
      (D : Real) < (s : Real) * ((rho : Real) + eps) ∧ 0 < D ∧
      ∃ m : Nat, ∃ g : Fin m → MvPolynomial (Fin d) Complex,
        (∀ j, g j ∈ I ^ s) ∧
        (∀ j, ∀ a ∈ (g j).support,
          ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
        (∀ i : Fin d, ∃ N : Nat, 0 < N ∧
          MvPolynomial.X i ^ N ∈ Ideal.span
            (Set.range (fun j =>
              MvPolynomial.weightedHomogeneousComponent
                (fun k => (w k : ℚ)) (D : ℚ) (g j)))) := by sorry
