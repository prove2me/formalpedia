-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_quotient_of_coordinate_powers_aux_a9fbb753_463b_437c_88bf_627d1569d537
-- name    : OAI.PiExponent.FormalInterpolation.finite_quotient_of_coordinate_powers_aux_a9fbb753_463b_437c_88bf_627d1569d537
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:57:39.378586+00:00
-- url     : https://prove2.me/theorems/09fe19b8-c1c9-4e3f-89c8-bf5772f8390c
-- title:
--   Finite quotient when coordinate powers vanish
-- statement:
--   If an ideal in a polynomial ring over ℂ in finitely many variables contains a positive power of each variable, then the quotient is finite as a ℂ-module.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.finite_quotient_of_coordinate_powers_aux_a9fbb753_463b_437c_88bf_627d1569d537 {d : Nat} (J : Ideal (MvPolynomial (Fin d) ℂ)) (hpow : ∀ i : Fin d, ∃ e : Nat, 0 < e ∧ (MvPolynomial.X i) ^ e ∈ J) : Module.Finite ℂ ((MvPolynomial (Fin d) ℂ) ⧸ J) := by sorry
