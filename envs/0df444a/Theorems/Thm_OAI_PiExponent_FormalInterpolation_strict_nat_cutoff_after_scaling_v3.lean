-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_strict_nat_cutoff_after_scaling_v3
-- name    : OAI.PiExponent.FormalInterpolation.strict_nat_cutoff_after_scaling_v3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T19:31:06.653529+00:00
-- url     : https://prove2.me/theorems/e2651ec3-6dae-4ca5-b9e5-b06b3de6b537
-- title:
--   Round scaled bounds below a strict cutoff (v3)
-- statement:
--   For finitely many real values strictly below the half-epsilon bound, choose a positive scale and a natural cutoff that bounds all scaled values and remains strictly below the full-epsilon bound. In dimension zero, `B = 0` works.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic

theorem OAI.PiExponent.FormalInterpolation.strict_nat_cutoff_after_scaling_v3
    {d : Nat} (s : Nat) (hs : 0 < s)
    (rho : Real) (hrho : 0 ≤ rho)
    (eps : Real) (heps : 0 < eps)
    (x : Fin d → Real)
    (hx : ∀ i, x i < (s : Real) * (rho + eps / 2)) :
    ∃ k : Nat, 0 < k ∧ ∃ B : Nat,
      (B : Real) < ((s * k : Nat) : Real) * (rho + eps) ∧
      ∀ i, x i * (k : Real) ≤ (B : Real) := by sorry
