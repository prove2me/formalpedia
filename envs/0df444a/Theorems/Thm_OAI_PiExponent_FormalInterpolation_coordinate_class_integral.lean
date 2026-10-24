-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_class_integral
-- name    : OAI.PiExponent.FormalInterpolation.coordinate_class_integral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T11:46:33.26199+00:00
-- url     : https://prove2.me/theorems/76059a2a-c9ff-4420-80a0-27877c9e6391
-- title:
--   Coordinate classes are integral
-- statement:
--   Each coordinate class in the quotient by the coordinate powers is integral over ℂ, since its specified positive power vanishes.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.coordinate_class_integral (d : Nat) (N : Fin d → Nat) (hN : ∀ i, 0 < N i) (i : Fin d) : IsIntegral ℂ (Ideal.Quotient.mk (Ideal.span (Set.range (fun j : Fin d => (MvPolynomial.X j : MvPolynomial (Fin d) ℂ) ^ N j))) (MvPolynomial.X i)) := by sorry
