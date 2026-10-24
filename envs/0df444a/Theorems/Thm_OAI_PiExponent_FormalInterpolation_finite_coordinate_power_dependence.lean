-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_coordinate_power_dependence
-- name    : OAI.PiExponent.FormalInterpolation.finite_coordinate_power_dependence
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:55:28.024979+00:00
-- url     : https://prove2.me/theorems/2b513017-8caf-47b0-beb1-5371a2845ac9
-- title:
--   Finite-dimensional quotient gives a dependence among coordinate powers
-- statement:
--   In a finite-dimensional polynomial quotient, some nontrivial finite linear combination of the classes of the powers of any fixed coordinate is zero. This is proved independently by linear dependence of more than `finrank` many vectors and the fact that the kernel of the quotient map is the ideal.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.finite_coordinate_power_dependence
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) ℂ))
    [Module.Finite ℂ (MvPolynomial (Fin d) ℂ ⧸ I)] (i : Fin d) :
    ∃ K : Nat, ∃ c : Fin (K + 1) → ℂ,
      (∃ n : Fin (K + 1), c n ≠ 0) ∧
      (∑ n : Fin (K + 1), MvPolynomial.C (c n) *
        (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ (n : Nat)) ∈ I := by sorry
