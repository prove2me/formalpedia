-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_curve_bound_gives_span_all_bounded_top_components
-- name    : OAI.PiExponent.FormalInterpolation.weighted_curve_bound_gives_span_all_bounded_top_components
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-23T08:29:15.19599+00:00
-- url     : https://prove2.me/theorems/f6947797-7f14-41f1-9bf8-bec5faf9c475
-- title:
--   Curve bound gives a basepoint-free ideal of bounded top components
-- statement:
--   Using the curve-contact bound and finite-colength hypothesis, find a positive ordinary power and a strict subcritical weighted cutoff such that the degree-cutoff components of all eligible bounded-weight elements generate an ideal containing a positive power of every coordinate.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.weighted_curve_bound_gives_span_all_bounded_top_components
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
            Ideal.span (Set.range (fun f :
              {p : MvPolynomial (Fin d) Complex //
                p ∈ I ^ s ∧
                ∀ a ∈ p.support,
                  ∑ k, (w k : Real) * (a k : Real) ≤ D} =>
              MvPolynomial.weightedHomogeneousComponent
                (fun k => (w k : Real)) D f.1)) := by sorry
