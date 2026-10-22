-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_curve_bound_gives_power_sections_at_infinity
-- name    : OAI.PiExponent.FormalInterpolation.weighted_curve_bound_gives_power_sections_at_infinity
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-21T09:19:38.516451+00:00
-- url     : https://prove2.me/theorems/9509aef6-0ff2-4a88-b6f6-23651df89705
-- title:
--   Curve bound supplies ideal-power sections without basepoints at infinity
-- statement:
--   For every slope R strictly above rho, a positive ordinary ideal power contains finitely many polynomials of weight at most D<sR whose common degree-D components generate an ideal containing a positive power of every coordinate. This is the finite certificate expressing absence of common basepoints at infinity.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.weighted_curve_bound_gives_power_sections_at_infinity
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (R : Real) (hR : (rho : Real) < R) :
    ∃ s : Nat, 0 < s ∧
      ∃ D : Real, 0 < D ∧ D < (s : Real) * R ∧
        ∃ k : Nat, ∃ f : Fin k → MvPolynomial (Fin d) Complex,
          (∀ j, f j ∈ I ^ s) ∧
          (∀ j, ∀ a ∈ (f j).support,
            ∑ i, (w i : Real) * (a i : Real) ≤ D) ∧
          (∀ i : Fin d, ∃ e : Nat, 0 < e ∧
            MvPolynomial.X i ^ e ∈
              Ideal.span (Set.range (fun j : Fin k =>
                MvPolynomial.weightedHomogeneousComponent
                  (fun i => (w i : Real)) D (f j)))) := by sorry
