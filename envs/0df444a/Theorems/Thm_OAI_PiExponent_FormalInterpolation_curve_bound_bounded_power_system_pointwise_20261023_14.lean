-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_curve_bound_bounded_power_system_pointwise_20261023_14
-- name    : OAI.PiExponent.FormalInterpolation.curve_bound_bounded_power_system_pointwise_20261023_14
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-23T17:43:33.692073+00:00
-- url     : https://prove2.me/theorems/45435595-a524-467d-8a3e-36f98c59c4d5
-- title:
--   Curve contact yields pointwise bounded sections
-- statement:
--   Choose uniform positive integers `s` and `D` under the strict slope bound so that every nonzero point admits a section in `I ^ s`, supported in weighted degree at most `D`, whose degree-`D` weighted component is nonzero there. This removes the geometric section-construction obligation from the parent. A concrete route is to derive positivity on the weighted blow-up from the curve-contact bound, then use asymptotic generation. The zero-dimensional case is vacuous; for positive dimension the strict numeric allowance is retained.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.curve_bound_bounded_power_system_pointwise_20261023_14
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
