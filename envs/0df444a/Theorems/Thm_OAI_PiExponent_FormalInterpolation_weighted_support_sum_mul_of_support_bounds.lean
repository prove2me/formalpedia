-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_support_sum_mul_of_support_bounds
-- name    : OAI.PiExponent.FormalInterpolation.weighted_support_sum_mul_of_support_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:53:30.781989+00:00
-- url     : https://prove2.me/theorems/2d1bf5d8-31a2-4c3c-8a78-bb149c6e65f1
-- title:
--   Support weights for a finite sum of products
-- statement:
--   Uniform bounds on support weights for each factor imply the sum bound for the support of the finite sum of pairwise products. Support containment and additive weights provide an independent proof route, including when some coordinate weights are negative.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.weighted_support_sum_mul_of_support_bounds
    {d t : Nat} (w : Fin d → Rat)
    (p q : Fin t → MvPolynomial (Fin d) Complex) (A B : Real)
    (hp : ∀ i, ∀ a ∈ (p i).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ A)
    (hq : ∀ i, ∀ a ∈ (q i).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ B) :
    ∀ a ∈ (∑ i : Fin t, p i * q i).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ A + B := by sorry
