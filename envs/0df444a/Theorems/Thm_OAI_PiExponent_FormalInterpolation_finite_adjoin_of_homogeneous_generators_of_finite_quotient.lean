-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_adjoin_of_homogeneous_generators_of_finite_quotient
-- name    : OAI.PiExponent.FormalInterpolation.finite_adjoin_of_homogeneous_generators_of_finite_quotient
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:43:07.512891+00:00
-- url     : https://prove2.me/theorems/69d831c4-41e7-46f4-bf5d-4410c7601e50
-- title:
--   Finite adjoin from a finite homogeneous quotient
-- statement:
--   For positive rational variable weights, if finitely many generators are homogeneous of the same positive weighted degree and their ideal has finite-dimensional quotient, then the polynomial ring is finite as a module over the algebra they generate.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.finite_adjoin_of_homogeneous_generators_of_finite_quotient
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) (D : ℚ))
    [Module.Finite ℂ (MvPolynomial (Fin d) ℂ ⧸ Ideal.span (Set.range p))] :
    Module.Finite (Algebra.adjoin ℂ (Set.range p)) (MvPolynomial (Fin d) ℂ) := by sorry
