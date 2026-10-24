-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_curve_bound_gives_finite_weighted_power_certificate
-- name    : OAI.PiExponent.FormalInterpolation.weighted_curve_bound_gives_finite_weighted_power_certificate
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-23T08:17:34.915064+00:00
-- url     : https://prove2.me/theorems/66810a25-dd66-4e4f-bcab-9a1c20f7f7db
-- title:
--   Curve bound yields a finite weighted power certificate
-- statement:
--   For a common positive power s and cutoff D strictly below sR, find a finite family of elements of I^s, each supported in weighted degree at most D, whose degree-D weighted homogeneous components generate a positive power of every coordinate.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.weighted_curve_bound_gives_finite_weighted_power_certificate
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (R : Real) (hR : (rho : Real) < R) :
    ∃ s : Nat, 0 < s ∧
      ∃ D : Real, 0 < D ∧ D < (s : Real) * R ∧
        ∃ n : Nat, ∃ f : Fin n → MvPolynomial (Fin d) Complex,
          (∀ j, f j ∈ I ^ s) ∧
          (∀ j, ∀ a ∈ (f j).support,
            ∑ k, (w k : Real) * (a k : Real) ≤ D) ∧
          ∀ i : Fin d, ∃ e : Nat, 0 < e ∧
            MvPolynomial.X i ^ e ∈
              Ideal.span (Set.range (fun j =>
                MvPolynomial.weightedHomogeneousComponent
                  (fun k => (w k : Real)) D (f j))) := by sorry
