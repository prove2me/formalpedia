-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_homogeneous_relation_implies_coordinate_nilpotent_v3
-- name    : OAI.PiExponent.FormalInterpolation.homogeneous_relation_implies_coordinate_nilpotent_v3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:04:23.421288+00:00
-- url     : https://prove2.me/theorems/eb11ddf5-572a-4a8d-912c-bf94275a94fe
-- title:
--   A homogeneous ideal isolates a coordinate power
-- statement:
--   A nonzero univariate relation in an ideal closed under weighted components forces a positive power of the variable into the ideal. If p has positive degree, take its component at weight natDegree(p)·w(i): positivity makes the powers' weights distinct, and the component is the nonzero leading coefficient times X(i)^natDegree(p). Divide by that invertible scalar. If p is constant, the relation puts a unit in I, so X(i) belongs to I.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.homogeneous_relation_implies_coordinate_nilpotent_v3
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (I : Ideal (MvPolynomial (Fin d) ℂ))
    (hcomponents : ∀ f : MvPolynomial (Fin d) ℂ, f ∈ I →
      ∀ r : ℚ, MvPolynomial.weightedHomogeneousComponent w r f ∈ I)
    (i : Fin d) (p : Polynomial ℂ) (hp : p ≠ 0)
    (hpI : Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X i) p ∈ I) :
    ∃ n : Nat, 0 < n ∧ (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n ∈ I := by sorry
