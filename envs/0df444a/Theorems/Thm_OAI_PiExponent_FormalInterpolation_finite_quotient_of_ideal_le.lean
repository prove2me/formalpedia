-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_quotient_of_ideal_le
-- name    : OAI.PiExponent.FormalInterpolation.finite_quotient_of_ideal_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T10:07:49.905516+00:00
-- url     : https://prove2.me/theorems/e5c58afc-2d6d-4b95-83fb-219410f77451
-- title:
--   Finiteness passes to quotients by larger ideals
-- statement:
--   If `J` is contained in `I` and the quotient by `J` is finite-dimensional, then the quotient by `I` is finite-dimensional.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.finite_quotient_of_ideal_le (d : Nat) (J I : Ideal (MvPolynomial (Fin d) ℂ)) (hJI : J ≤ I) (hJ : Module.Finite ℂ (MvPolynomial (Fin d) ℂ ⧸ J)) : Module.Finite ℂ (MvPolynomial (Fin d) ℂ ⧸ I) := by sorry
