-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_graded_quotient_coordinate_nilpotent
-- name    : OAI.PiExponent.FormalInterpolation.finite_graded_quotient_coordinate_nilpotent
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T11:45:48.193222+00:00
-- url     : https://prove2.me/theorems/0095f004-2dc2-4674-b658-4b4feb1c3060
-- title:
--   Coordinates are nilpotent in a finite dimensional graded quotient
-- statement:
--   For strictly positive rational coordinate weights, if an ideal is closed under weighted homogeneous components and its polynomial-ring quotient is finite dimensional over ℂ, then a positive power of each coordinate belongs to the ideal.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.finite_graded_quotient_coordinate_nilpotent
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (I : Ideal (MvPolynomial (Fin d) ℂ))
    (hcomponents : ∀ f : MvPolynomial (Fin d) ℂ, f ∈ I →
      ∀ r : ℚ,
        MvPolynomial.weightedHomogeneousComponent w r f ∈ I)
    (hquot : Module.Finite ℂ (MvPolynomial (Fin d) ℂ ⧸ I)) :
    ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
      (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n ∈ I := by sorry
