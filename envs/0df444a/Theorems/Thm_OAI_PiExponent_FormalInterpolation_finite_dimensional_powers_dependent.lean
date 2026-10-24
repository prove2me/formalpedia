-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_dimensional_powers_dependent
-- name    : OAI.PiExponent.FormalInterpolation.finite_dimensional_powers_dependent
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T10:00:09.29643+00:00
-- url     : https://prove2.me/theorems/79539165-4ae3-4d6e-9e0b-8ba983e63752
-- title:
--   Powers in a finite-dimensional algebra are linearly dependent
-- statement:
--   For every element of a finite-dimensional commutative ℂ-algebra, some finite linear combination of its powers is zero with at least one nonzero coefficient.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.finite_dimensional_powers_dependent
    {A : Type*} [CommRing A] [Algebra ℂ A] [Module.Finite ℂ A] (a : A) :
    ∃ K : Nat, ∃ c : Fin (K + 1) → ℂ,
      (∃ n : Fin (K + 1), c n ≠ 0) ∧
      (∑ n : Fin (K + 1), algebraMap ℂ A (c n) * a ^ (n : Nat)) = 0 := by sorry
