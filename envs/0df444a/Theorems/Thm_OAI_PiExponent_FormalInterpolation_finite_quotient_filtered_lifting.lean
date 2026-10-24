-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_quotient_filtered_lifting
-- name    : OAI.PiExponent.FormalInterpolation.finite_quotient_filtered_lifting
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T10:00:41.804142+00:00
-- url     : https://prove2.me/theorems/1f553975-403b-4c14-8156-c2f31b7cdb63
-- title:
--   Lift a finite homogeneous quotient to module finiteness
-- statement:
--   For strictly positive rational coordinate weights, homogeneous generators of one positive weighted degree make the polynomial ring finite as a module over the generated algebra whenever their ideal has finite-dimensional quotient.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.finite_quotient_filtered_lifting
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) (D : ℚ))
    (hquot : Module.Finite ℂ
      (MvPolynomial (Fin d) ℂ ⧸ Ideal.span (Set.range p))) :
    Module.Finite (Algebra.adjoin ℂ (Set.range p)) (MvPolynomial (Fin d) ℂ) := by sorry
