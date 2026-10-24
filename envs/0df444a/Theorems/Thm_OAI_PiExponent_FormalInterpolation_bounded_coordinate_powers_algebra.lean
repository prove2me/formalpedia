-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_coordinate_powers_algebra
-- name    : OAI.PiExponent.FormalInterpolation.bounded_coordinate_powers_algebra
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T19:27:01.663645+00:00
-- url     : https://prove2.me/theorems/899b2aa1-7a70-4232-9736-3ab99e5e4612
-- title:
--   Exact-degree coordinate powers lie in the generated span
-- statement:
--   For a common exact weighted degree and coordinate exponents above the scaled original exponents, prove the target conclusion using closure of ideal powers under multiplication and the weighted homogeneous component of a monomial.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.bounded_coordinate_powers_algebra
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (R : Real)
    (hw : ∀ i, 0 < (w i : Real))
    (s : Nat) (hs : 0 < s) (B : Nat)
    (q D : Nat) (hq : 0 < q) (hDpos : 0 < D)
    (hDcut : (D : Real) < ((s * q : Nat) : Real) * R)
    (hcommon : ∀ i : Fin d, ∃ n : Nat, ∃ m : Nat,
      0 < n ∧ MvPolynomial.X i ^ n ∈ I ^ s ∧
      (n : Real) * (w i : Real) ≤ (B : Real) ∧
      q * n ≤ m ∧ 0 < m ∧
      (m : Real) * (w i : Real) = (D : Real)) :
    ∃ s' : Nat, 0 < s' ∧ ∃ D' : Nat,
      (D' : Real) < (s' : Real) * R ∧
      0 < D' ∧
      ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
        MvPolynomial.X i ^ n ∈ Ideal.span
          {h : MvPolynomial (Fin d) Complex |
            ∃ g : MvPolynomial (Fin d) Complex,
              g ∈ I ^ s' ∧
              (∀ a ∈ g.support,
                ∑ k, (w k : Real) * (a k : Real) ≤ (D' : Real)) ∧
              h = MvPolynomial.weightedHomogeneousComponent
                (fun k => (w k : ℚ)) (D' : ℚ) g} := by sorry
