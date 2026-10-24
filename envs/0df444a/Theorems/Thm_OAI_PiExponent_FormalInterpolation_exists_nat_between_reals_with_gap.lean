-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_exists_nat_between_reals_with_gap
-- name    : OAI.PiExponent.FormalInterpolation.exists_nat_between_reals_with_gap
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T19:35:08.687707+00:00
-- url     : https://prove2.me/theorems/b73f73b1-eb42-4bf4-84d1-cb531e9c75e8
-- title:
--   A natural number fits inside a real interval wider than one
-- statement:
--   For a nonnegative real lower bound, if the upper bound lies strictly more than one above it, a natural number lies in the half-open interval from the lower bound to the upper bound.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic

theorem OAI.PiExponent.FormalInterpolation.exists_nat_between_reals_with_gap {a b : Real} (ha : 0 ≤ a) (hab : a + 1 < b) : ∃ n : Nat, a ≤ (n : Real) ∧ (n : Real) < b := by sorry
