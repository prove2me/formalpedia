-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_curve_bound_bounded_power_system_pointwise_20261023_12
-- name    : OAI.PiExponent.FormalInterpolation.curve_bound_bounded_power_system_pointwise_20261023_12
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-23T17:37:20.993832+00:00
-- url     : https://prove2.me/theorems/9ad71ff0-b823-440e-96fe-f7e42d33b754
-- title:
--   Curve contact yields pointwise bounded sections
-- statement:
--   Choose uniform positive integers `s` and `D` with the target’s strict quantitative bound so that every nonzero point has some section in `I ^ s`, supported in weighted degree at most `D`, whose degree-`D` weighted component does not vanish there. This isolates the geometric basepoint-free construction before finite witness extraction.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.curve_bound_bounded_power_system_pointwise_20261023_12
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∃ s : Nat, 0 < s ∧ ∃ D : Nat,
      (D : Real) < (s : Real) * ((rho : Real) + eps) ∧ 0 < D ∧
      ∀ (x : Fin d → Complex), (∃ i : Fin d, x i ≠ 0) →
        ∃ p : MvPolynomial (Fin d) Complex,
          p ∈ I ^ s ∧
          (∀ a ∈ p.support,
            ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
          MvPolynomial.eval x
            (MvPolynomial.weightedHomogeneousComponent
              (fun k => (w k : ℚ)) (D : ℚ) p) ≠ 0 := by sorry
