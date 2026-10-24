-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_coordinate_powers_to_exact_initial_ideal
-- name    : OAI.PiExponent.FormalInterpolation.bounded_coordinate_powers_to_exact_initial_ideal
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-23T19:08:54.325069+00:00
-- url     : https://prove2.me/theorems/79032779-9609-4132-a26c-ded99f5aa7c8
-- title:
--   Bounded coordinate monomials give an exact-degree initial ideal
-- statement:
--   Given coordinate monomial powers in one ordinary ideal power with weighted degrees below a strict linear cutoff, align them at one positive integer weighted degree while preserving the strict cutoff. A proof uses a common integer multiple of the rational weights, raises the ideal power to create room for the bounded rounding overhead, and multiplies each coordinate monomial to that common degree. When there are no coordinates, choose the positive numerical witnesses from the strict slack.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.bounded_coordinate_powers_to_exact_initial_ideal
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (R : Real)
    (hsections : ∃ s : Nat, 0 < s ∧ ∃ B : Nat,
      (B : Real) < (s : Real) * R ∧
      ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
        MvPolynomial.X i ^ n ∈ I ^ s ∧
        (n : Real) * (w i : Real) ≤ (B : Real)) :
    ∃ s : Nat, 0 < s ∧ ∃ D : Nat,
      (D : Real) < (s : Real) * R ∧
      0 < D ∧
      ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
        MvPolynomial.X i ^ n ∈ Ideal.span
          {h : MvPolynomial (Fin d) Complex |
            ∃ g : MvPolynomial (Fin d) Complex,
              g ∈ I ^ s ∧
              (∀ a ∈ g.support,
                ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
              h = MvPolynomial.weightedHomogeneousComponent
                (fun k => (w k : ℚ)) (D : ℚ) g} := by sorry
