-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_finite_power_certificate_to_rational_initial_power_certificate
-- name    : OAI.PiExponent.FormalInterpolation.weighted_finite_power_certificate_to_rational_initial_power_certificate
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-24T14:28:18.433052+00:00
-- url     : https://prove2.me/theorems/697b9542-c582-4208-83ba-a23b09104527
-- title:
--   Power up a real-cutoff certificate to a rational strict cutoff
-- statement:
--   Given a finite family in a positive ordinary ideal power, with support below a positive real cutoff and cutoff components generating a positive power of each coordinate, raise the family to a common product power and choose a positive rational strict cutoff with an additive margin of one, retaining coordinate-power generation.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.weighted_finite_power_certificate_to_rational_initial_power_certificate
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (rho : Rat) (eps : Real) (heps : 0 < eps)
    (s : Nat) (hs : 0 < s) (D : Real) (hD : 0 < D)
    (hDtarget : D < (s : Real) * ((rho : Real) + eps))
    (n : Nat) (f : Fin n → MvPolynomial (Fin d) Complex)
    (hf : ∀ j, f j ∈ I ^ s)
    (hweight : ∀ j, ∀ a ∈ (f j).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ D)
    (hgen : ∀ i : Fin d, ∃ e : Nat, 0 < e ∧
      MvPolynomial.X i ^ e ∈
        Ideal.span (Set.range (fun j =>
          MvPolynomial.weightedHomogeneousComponent
            (fun k => (w k : Real)) D (f j)))) :
    ∃ q : Rat, 0 < q ∧ (q : Real) + 1 <
      (s : Real) * ((rho : Real) + eps) ∧
      ∃ n' : Nat, ∃ g : Fin n' → MvPolynomial (Fin d) Complex,
        (∀ j, g j ∈ I ^ s) ∧
        (∀ j, ∀ a ∈ (g j).support,
          ∑ k, (w k : Real) * (a k : Real) ≤ (q : Real)) ∧
        ∀ i : Fin d, ∃ e : Nat,
          MvPolynomial.X i ^ e ∈
            Ideal.span (Set.range (fun j =>
              MvPolynomial.weightedHomogeneousComponent
                (fun k => (w k : ℝ)) q (g j))) := by sorry
