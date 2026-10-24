-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_adjoin_of_coordinate_powers
-- name    : OAI.PiExponent.FormalInterpolation.finite_adjoin_of_coordinate_powers
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:51:08.700992+00:00
-- url     : https://prove2.me/theorems/8025afa7-a3af-4fd4-811e-699401e068d0
-- title:
--   Finite adjoin from coordinate-power relations
-- statement:
--   If the generators are homogeneous of the same positive weighted degree and a positive power of each variable belongs to their ideal, then the polynomial ring is a finite module over the algebra they generate.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.finite_adjoin_of_coordinate_powers
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) (D : ℚ))
    (hpow : ∀ i : Fin d, ∃ N : Nat, 0 < N ∧
      (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ N ∈ Ideal.span (Set.range p)) :
    Module.Finite (Algebra.adjoin ℂ (Set.range p)) (MvPolynomial (Fin d) ℂ) := by sorry
