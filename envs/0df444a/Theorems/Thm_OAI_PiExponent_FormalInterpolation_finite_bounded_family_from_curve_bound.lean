-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_bounded_family_from_curve_bound
-- name    : OAI.PiExponent.FormalInterpolation.finite_bounded_family_from_curve_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-23T08:38:25.253411+00:00
-- url     : https://prove2.me/theorems/f10af962-9ab7-4d39-84ba-157e583c9d2f
-- title:
--   Curve contact yields a subcritical finite algebra family
-- statement:
--   A weighted curve-contact bound with finite-colength quotient yields a finite family of bounded-weight elements in an ordinary power of the ideal, generating a subalgebra over which the polynomial ring is finite, with a strict subcritical degree-to-power ratio.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.finite_bounded_family_from_curve_bound
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∃ s : Nat, 0 < s ∧ ∃ D : Nat, (D : Real) < (s : Real) * ((rho : Real) + eps) ∧
      ∃ m : Nat, ∃ g : Fin m → MvPolynomial (Fin d) Complex,
        (∀ j, g j ∈ I ^ s) ∧
        (∀ j, ∀ a ∈ (g j).support,
          ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
        Module.Finite (Algebra.adjoin Complex (Set.range g))
          (MvPolynomial (Fin d) Complex) := by sorry
