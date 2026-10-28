-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_scale_rational_weighted_power_certificate
-- name    : OAI.PiExponent.FormalInterpolation.scale_rational_weighted_power_certificate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T14:46:52.669495+00:00
-- url     : https://prove2.me/theorems/551d2788-4d8d-41f8-a8d0-79db0963584d
-- title:
--   Scale a rational-cutoff weighted power certificate
-- statement:
--   From a finite weighted certificate at rational cutoff D with D < sR, form a new certificate at a scaled power and cutoff q = kD so that q + 1 is strictly below the scaled bound. Index the new family by all k-fold products of the original family; the degree bound scales, and the powered coordinate memberships follow from the original generated-ideal memberships.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weightedHomogeneousComponent_rat_eq_real

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.scale_rational_weighted_power_certificate
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (R : Real)
    (s : Nat) (hs : 0 < s) (D : Real) (hD : 0 < D)
    (hDR : D < (s : Real) * R) (r : Rat) (hr : (r : Real) = D)
    (n : Nat) (f : Fin n → MvPolynomial (Fin d) Complex)
    (hf : ∀ j, f j ∈ I ^ s)
    (hweight : ∀ j, ∀ a ∈ (f j).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ D)
    (hgen : ∀ i : Fin d, ∃ e : Nat, 0 < e ∧
      MvPolynomial.X i ^ e ∈ Ideal.span (Set.range (fun j =>
        MvPolynomial.weightedHomogeneousComponent
          (fun k => (w k : Real)) D (f j)))) :
    ∃ s' : Nat, 0 < s' ∧ ∃ q : Rat, 0 < q ∧
      (q : Real) + 1 < (s' : Real) * R ∧
      ∃ n' : Nat, ∃ g : Fin n' → MvPolynomial (Fin d) Complex,
        (∀ j, g j ∈ I ^ s') ∧
        (∀ j, ∀ a ∈ (g j).support,
          ∑ k, (w k : Real) * (a k : Real) ≤ (q : Real)) ∧
        ∀ i : Fin d, ∃ e : Nat,
          MvPolynomial.X i ^ e ∈ Ideal.span (Set.range (fun j =>
            MvPolynomial.weightedHomogeneousComponent w q (g j))) := by sorry
