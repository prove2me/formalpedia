-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_scaled_product_algebraic_certificate
-- name    : OAI.PiExponent.FormalInterpolation.scaled_product_algebraic_certificate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T14:59:09.460651+00:00
-- url     : https://prove2.me/theorems/fef55da7-79c2-424f-9312-f89b3ac13d00
-- title:
--   Build the scaled certificate from products
-- statement:
--   For positive k, form a finite family of all k-fold products of the original sections. It lies in I^(ks), has support weights at most kr, and its exact kr weighted components generate a power of every coordinate variable.
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

theorem OAI.PiExponent.FormalInterpolation.scaled_product_algebraic_certificate
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (s : Nat) (hs : 0 < s) (D : Real)
    (hD : 0 < D) (r : Rat) (hr : (r : Real) = D)
    (k : Nat) (hk : 0 < k) (n : Nat)
    (f : Fin n → MvPolynomial (Fin d) Complex)
    (hf : ∀ j, f j ∈ I ^ s)
    (hweight : ∀ j, ∀ a ∈ (f j).support,
      ∑ l, (w l : Real) * (a l : Real) ≤ D)
    (hgen : ∀ i : Fin d, ∃ e : Nat, 0 < e ∧
      MvPolynomial.X i ^ e ∈ Ideal.span (Set.range (fun j =>
        MvPolynomial.weightedHomogeneousComponent
          (fun l => (w l : Real)) D (f j)))) :
    0 < k * r ∧
    ∃ n' : Nat, ∃ g : Fin n' → MvPolynomial (Fin d) Complex,
      (∀ j, g j ∈ I ^ (k * s)) ∧
      (∀ j, ∀ a ∈ (g j).support,
        ∑ l, (w l : Real) * (a l : Real) ≤ ((k * r : Rat) : Real)) ∧
      ∀ i : Fin d, ∃ e : Nat,
        MvPolynomial.X i ^ e ∈ Ideal.span (Set.range (fun j =>
          MvPolynomial.weightedHomogeneousComponent (w) (k * r) (g j))) := by sorry
