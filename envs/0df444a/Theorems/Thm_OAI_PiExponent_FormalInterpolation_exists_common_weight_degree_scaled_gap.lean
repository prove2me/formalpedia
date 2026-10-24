-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_exists_common_weight_degree_scaled_gap
-- name    : OAI.PiExponent.FormalInterpolation.exists_common_weight_degree.scaled_gap
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:57:52.228536+00:00
-- url     : https://prove2.me/theorems/cb70ddd4-e02a-460e-ac1e-60cb34e924f2
-- title:
--   Scaled integer multiples enter a strict real interval
-- statement:
--   For a positive degree quantum and a strict positive interval, choose an integer scale and a positive integer multiple of the quantum strictly above the scaled lower endpoint plus the fixed nonnegative allowance and strictly below the scaled upper endpoint.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic

theorem OAI.PiExponent.FormalInterpolation.exists_common_weight_degree.scaled_gap
    (q : Real) (hq : 0 < q)
    (lo : Real) (hlo : 0 < lo) (R : Real) (hgap : lo < R)
    (C : Real) (hC : 0 ≤ C) (N : Nat) :
    ∃ s : Nat, 0 < s ∧ N ≤ s ∧
      ∃ D : Real, 0 < D ∧
        (s : Real) * lo + C < D ∧
        D < (s : Real) * R ∧
        ∃ k : Nat, 0 < k ∧ D = (k : Real) * q := by sorry
