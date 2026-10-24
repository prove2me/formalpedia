-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_coordinate_powers_to_exact_initial_ideal_positive_weights
-- name    : OAI.PiExponent.FormalInterpolation.bounded_coordinate_powers_to_exact_initial_ideal_positive_weights
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T19:20:21.53343+00:00
-- url     : https://prove2.me/theorems/69de97b2-0266-461c-ab76-87d998c4b8ae
-- title:
--   Positive weights align bounded coordinate powers at one exact degree
-- statement:
--   For strictly positive rational weights, coordinate monomial powers in one ordinary ideal power with weighted degrees below a strict linear cutoff can be aligned at one positive integer weighted degree. Raising the ideal-power exponent creates room for rounding to a common degree lattice; multiplying each coordinate monomial to that degree preserves membership in the ordinary ideal power and makes it an exact-degree component. In dimension zero, only the numerical witnesses remain.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.bounded_coordinate_powers_to_exact_initial_ideal_positive_weights
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (R : Real)
    (hw : ∀ i, 0 < (w i : Real))
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
