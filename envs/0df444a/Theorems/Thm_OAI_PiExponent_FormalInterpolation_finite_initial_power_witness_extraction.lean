-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_initial_power_witness_extraction
-- name    : OAI.PiExponent.FormalInterpolation.finite_initial_power_witness_extraction
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:20:33.514549+00:00
-- url     : https://prove2.me/theorems/d0b7e6b5-1bf5-4048-8414-1b0ea6b2bc06
-- title:
--   Extract finite bounded sections from initial ideal memberships
-- statement:
--   For fixed positive `s` and `D`, if each coordinate has a positive power in the span of degree-`D` components of bounded-weight elements of `I^s`, then finitely many such elements suffice simultaneously for all coordinates, retaining their ideal-power and support-weight bounds.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.finite_initial_power_witness_extraction
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat)
    (s : Nat) (hs : 0 < s)
    (D : Real) (hD : 0 < D)
    (hinitial : ∀ i : Fin d, ∃ e : Nat, 0 < e ∧
      MvPolynomial.X i ^ e ∈
        Ideal.span (Set.range (fun (p :
          {g : MvPolynomial (Fin d) Complex //
            g ∈ I ^ s ∧
            ∀ a ∈ g.support,
              ∑ j, (w j : Real) * (a j : Real) ≤ D}) =>
          MvPolynomial.weightedHomogeneousComponent
            (fun j => (w j : Real)) D p.1))) :
    ∃ k : Nat, ∃ f : Fin k → MvPolynomial (Fin d) Complex,
      (∀ j, f j ∈ I ^ s) ∧
      (∀ j, ∀ a ∈ (f j).support,
        ∑ i, (w i : Real) * (a i : Real) ≤ D) ∧
      (∀ i : Fin d, ∃ e : Nat, 0 < e ∧
        MvPolynomial.X i ^ e ∈
          Ideal.span (Set.range (fun j : Fin k =>
            MvPolynomial.weightedHomogeneousComponent
              (fun i => (w i : Real)) D (f j)))) := by sorry
