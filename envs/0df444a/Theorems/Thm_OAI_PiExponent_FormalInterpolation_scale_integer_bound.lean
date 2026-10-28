-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_scale_integer_bound
-- name    : OAI.PiExponent.FormalInterpolation.scale_integer_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T14:58:53.450408+00:00
-- url     : https://prove2.me/theorems/f2270d19-6f66-4e5d-a38f-e076c04b7dce
-- title:
--   Choose an integer scale with strict additive slack
-- statement:
--   Given the strict gap between D and sR and D positive, choose a positive integer scale k for which kD+1 is strictly less than (ks)R.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic

theorem OAI.PiExponent.FormalInterpolation.scale_integer_bound
    {s : Nat} (hs : 0 < s) {D R : Real} (hD : 0 < D)
    (hDR : D < (s : Real) * R) :
    ∃ k : Nat, 0 < k ∧ (k : Real) * D + 1 < ((k * s : Nat) : Real) * R := by sorry
