-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_quotient_of_ideal_le_a9fbb753_463b_437c_88bf_627d1569d537
-- name    : OAI.PiExponent.FormalInterpolation.finite_quotient_of_ideal_le_a9fbb753_463b_437c_88bf_627d1569d537
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:52:48.457544+00:00
-- url     : https://prove2.me/theorems/f22c1aa3-0366-4e54-b54b-81a70e5e7d37
-- title:
--   Finite quotient descends along ideal inclusion
-- statement:
--   If `J` is contained in `I` and the polynomial-ring quotient by `J` is finite as a complex module, then the quotient by `I` is finite as a complex module.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.finite_quotient_of_ideal_le_a9fbb753_463b_437c_88bf_627d1569d537 {d : Nat} (J I : Ideal (MvPolynomial (Fin d) ℂ)) (hJI : J ≤ I) (hfin : Module.Finite ℂ (MvPolynomial (Fin d) ℂ ⧸ J)) : Module.Finite ℂ (MvPolynomial (Fin d) ℂ ⧸ I) := by sorry
