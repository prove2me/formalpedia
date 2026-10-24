-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_curve_bound_bounded_power_system_origin_support_geometry_20261023_10
-- name    : OAI.PiExponent.FormalInterpolation.curve_bound_bounded_power_system_origin_support_geometry_20261023_10
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-23T17:26:36.308362+00:00
-- url     : https://prove2.me/theorems/6ab6bfea-930b-4f7f-8213-336566fc918f
-- title:
--   Curve contact yields bounded sections whose weighted components vanish only at the origin
-- statement:
--   Construct a positive ordinary power I^s and a finite family in it with support degrees bounded by D < s (rho + eps), such that the common zero locus of their degree-D weighted components lies in the origin. This isolates the geometric interpolation and ordinary-power section construction from the algebraic Nullstellensatz step.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.curve_bound_bounded_power_system_origin_support_geometry_20261023_10
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
        (∀ (x : Fin d → Complex),
          (∀ j : Fin m, MvPolynomial.eval x
            (MvPolynomial.weightedHomogeneousComponent
              (fun k => (w k : ℚ)) (D : ℚ) (g j)) = 0) →
          ∀ i : Fin d, x i = 0) := by sorry
