-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_curve_bound_pointwise_sections_20261023_17
-- name    : OAI.PiExponent.FormalInterpolation.curve_bound_pointwise_sections_20261023_17
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-23T18:22:31.006789+00:00
-- url     : https://prove2.me/theorems/21cf0110-2983-423d-8866-dad500519af0
-- title:
--   Curve contact produces pointwise bounded ordinary-power sections
-- statement:
--   Under the finite quotient and positive-weight hypotheses, the curve-contact bound yields uniform positive integers s and D with the strict subcritical degree allowance, and for every nonzero point a polynomial in I^s whose support is bounded by D and whose degree-D weighted component does not vanish there. This is the geometric core left to prove.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.curve_bound_pointwise_sections_20261023_17
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
