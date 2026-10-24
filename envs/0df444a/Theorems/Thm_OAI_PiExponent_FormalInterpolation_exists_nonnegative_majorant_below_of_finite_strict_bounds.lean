-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_exists_nonnegative_majorant_below_of_finite_strict_bounds
-- name    : OAI.PiExponent.FormalInterpolation.exists_nonnegative_majorant_below_of_finite_strict_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T19:34:49.943831+00:00
-- url     : https://prove2.me/theorems/fc988213-733c-4b84-b614-6cc2414ec4bb
-- title:
--   Finite strict bounds admit a nonnegative envelope
-- statement:
--   If finitely many real values are strictly below a positive bound, there is a nonnegative real envelope that bounds all of them and remains strictly below that bound. For the empty family, zero is such an envelope.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic

theorem OAI.PiExponent.FormalInterpolation.exists_nonnegative_majorant_below_of_finite_strict_bounds {d : Nat} (x : Fin d → Real) {c : Real} (hc : 0 < c) (hx : ∀ i, x i < c) : ∃ M : Real, 0 ≤ M ∧ (∀ i, x i ≤ M) ∧ M < c := by sorry
