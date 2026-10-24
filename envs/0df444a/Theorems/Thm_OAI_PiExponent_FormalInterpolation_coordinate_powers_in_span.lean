-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_powers_in_span
-- name    : OAI.PiExponent.FormalInterpolation.coordinate_powers_in_span
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T10:07:29.766304+00:00
-- url     : https://prove2.me/theorems/8d0745eb-01d9-4670-a6b6-7b9fcc1b6ad7
-- title:
--   Finite homogeneous quotient contains powers of every coordinate
-- statement:
--   For a positively weighted polynomial ring, if a finite list of common positive-degree homogeneous polynomials generates an ideal with finite-dimensional quotient, then a positive power of each coordinate belongs to that ideal.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.coordinate_powers_in_span {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ)) (D : Nat) (hD : 0 < D) (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ) (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) (D : ℚ)) (hquot : Module.Finite ℂ (MvPolynomial (Fin d) ℂ ⧸ Ideal.span (Set.range p))) : ∀ i : Fin d, ∃ n : Nat, 0 < n ∧ (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n ∈ Ideal.span (Set.range p) := by sorry
