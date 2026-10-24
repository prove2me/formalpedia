-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_curve_bound_bounded_power_system_geometric_certificate_ad07d61a_36d8_43a7_8c61_8455336fb8e7
-- name    : OAI.PiExponent.FormalInterpolation.curve_bound_bounded_power_system_geometric_certificate_ad07d61a_36d8_43a7_8c61_8455336fb8e7
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-23T14:33:30.590761+00:00
-- url     : https://prove2.me/theorems/23dfc97e-4e0b-44f8-a77e-d6671d289afa
-- title:
--   Curve contact yields a bounded family with origin-supported weighted components
-- statement:
--   Produce a positive ordinary power I^s and a finite family in it whose supports have weighted degree at most D, where D < s(rho + eps) and D > 0, and whose degree-D weighted components have common zero locus contained in the origin. This isolates the quantitative geometric construction while retaining the ordinary-power and strict-slope requirements. A route suggested by the research notes is compactification, blowup, curve-contact control, and ample-twist section extraction, followed by recovery of ordinary powers. Integral-closure estimates alone do not establish this statement; the geometric construction remains the core obligation.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.curve_bound_bounded_power_system_geometric_certificate_ad07d61a_36d8_43a7_8c61_8455336fb8e7
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
          (∀ j, MvPolynomial.eval x
            (MvPolynomial.weightedHomogeneousComponent
              (fun k => (w k : ℚ)) (D : ℚ) (g j)) = 0) →
          ∀ i : Fin d, x i = 0) := by sorry
