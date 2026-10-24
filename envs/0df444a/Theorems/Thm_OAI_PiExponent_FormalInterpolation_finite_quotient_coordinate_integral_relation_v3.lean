-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_quotient_coordinate_integral_relation_v3
-- name    : OAI.PiExponent.FormalInterpolation.finite_quotient_coordinate_integral_relation_v3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:04:05.584114+00:00
-- url     : https://prove2.me/theorems/5cdeaab1-a698-46f6-bab1-899a70b8f9f8
-- title:
--   Finite quotient gives a coordinate polynomial relation
-- statement:
--   Every coordinate class in the finite-dimensional quotient satisfies a nonzero univariate polynomial relation. This isolates the integrality and quotient-map step. Prove it by taking a monic annihilating polynomial for the coordinate class, then translating its vanishing through the quotient map; monicity ensures the polynomial is nonzero.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.finite_quotient_coordinate_integral_relation_v3
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) ℂ))
    (hquot : Module.Finite ℂ (MvPolynomial (Fin d) ℂ ⧸ I))
    (i : Fin d) :
    ∃ p : Polynomial ℂ, p ≠ 0 ∧
      Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X i) p ∈ I := by sorry
