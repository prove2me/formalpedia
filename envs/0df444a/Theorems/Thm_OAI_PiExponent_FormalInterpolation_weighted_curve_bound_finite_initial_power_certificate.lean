-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_curve_bound_finite_initial_power_certificate
-- name    : OAI.PiExponent.FormalInterpolation.weighted_curve_bound_finite_initial_power_certificate
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-24T09:09:31.038586+00:00
-- url     : https://prove2.me/theorems/9274670c-df1f-4fb4-9e9b-1fd348d56f2e
-- title:
--   Curve bound yields a finite strict-cutoff initial-power certificate
-- statement:
--   For every positive slack, produce one positive ordinary power and one positive rational weighted cutoff below the strict bound, together with finitely many sections in that ordinary power, all supported below the cutoff, whose cutoff components generate a power of each coordinate.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.weighted_curve_bound_finite_initial_power_certificate
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∃ s : Nat, 0 < s ∧ ∃ q : Rat, 0 < q ∧
      (q : Real) + 1 < (s : Real) * ((rho : Real) + eps) ∧
      ∃ n : Nat, ∃ f : Fin n → MvPolynomial (Fin d) Complex,
        (∀ j, f j ∈ I ^ s) ∧
        (∀ j, ∀ a ∈ (f j).support,
          ∑ k, (w k : Real) * (a k : Real) ≤ (q : Real)) ∧
        ∀ i : Fin d, ∃ e : Nat,
          MvPolynomial.X i ^ e ∈
            Ideal.span (Set.range (fun j =>
              MvPolynomial.weightedHomogeneousComponent
                (fun k => (w k : ℚ)) q (f j))) := by sorry
