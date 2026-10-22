-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_curve_bound_gives_power_sections_asymptotic_initial_power
-- name    : OAI.PiExponent.FormalInterpolation.weighted_curve_bound_gives_power_sections_asymptotic_initial_power
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-21T09:33:09.041003+00:00
-- url     : https://prove2.me/theorems/a9d056b5-d6cf-4bbb-9134-a87a91155170
-- title:
--   Curve bound yields a strict weighted cutoff with no initial basepoints
-- statement:
--   For some positive ideal power and a positive weighted cutoff strictly below sR, the degree-D components of all elements of that power with support weight at most D generate an ideal containing a positive power of every coordinate.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.weighted_curve_bound_gives_power_sections_asymptotic_initial_power
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (R : Real) (hR : (rho : Real) < R) :
    ∃ s : Nat, 0 < s ∧
      ∃ D : Real, 0 < D ∧ D < (s : Real) * R ∧
        ∀ i : Fin d, ∃ e : Nat, 0 < e ∧
          MvPolynomial.X i ^ e ∈
            Ideal.span (Set.range (fun p :
              {g : MvPolynomial (Fin d) Complex //
                g ∈ I ^ s ∧
                ∀ a ∈ g.support,
                  ∑ j, (w j : Real) * (a j : Real) ≤ D} =>
              MvPolynomial.weightedHomogeneousComponent
                (fun j => (w j : Real)) D p.1)) := by sorry
