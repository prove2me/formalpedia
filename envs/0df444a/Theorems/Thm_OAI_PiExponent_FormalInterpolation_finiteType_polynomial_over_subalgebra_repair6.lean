-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finiteType_polynomial_over_subalgebra_repair6
-- name    : OAI.PiExponent.FormalInterpolation.finiteType_polynomial_over_subalgebra_repair6
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:37:16.39144+00:00
-- url     : https://prove2.me/theorems/dd32cb34-b7ab-4e54-a0d4-24c89337f37b
-- title:
--   The polynomial algebra is finite type over a coefficient subalgebra
-- statement:
--   For any Complex-subalgebra A of the multivariate polynomial algebra, that algebra is finite type over A.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.finiteType_polynomial_over_subalgebra_repair6
    {d : Nat} (A : Subalgebra Complex (MvPolynomial (Fin d) Complex)) :
    Algebra.FiniteType A (MvPolynomial (Fin d) Complex) := by sorry
