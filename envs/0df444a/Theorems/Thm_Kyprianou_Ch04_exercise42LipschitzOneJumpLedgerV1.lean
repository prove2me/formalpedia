-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzOneJumpLedgerV1
-- name    : Kyprianou.Ch04.exercise42LipschitzOneJumpLedgerV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:32:09.678939+00:00
-- url     : https://prove2.me/theorems/d0cdc3eb-479c-4123-901e-be71d3f3d5da
-- title:
--   One-jump two-coordinate ledger with Lipschitz first coordinate
-- statement:
--   The two-coordinate change-of-variables identity for an affine drift path with one downward or upward jump, using a Lipschitz nonnegative first coordinate and explicit pre-jump, jump and post-jump contributions.
-- source:
--   Supporting deterministic finite-jump calculus for Kyprianou (2006), Chapter 4, Exercise 4.2.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzAffineSegmentChainV1
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise42LipschitzOneJumpLedgerV1
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (U : ℝ → ℝ) (K : ℝ≥0) (hU : LipschitzWith K U)
    (a c j κ T : ℝ) (hκ0 : 0 ≤ κ) (hκT : κ ≤ T)
    (hNonneg : ∀ s ∈ Set.Icc (0 : ℝ) T, 0 ≤ U s)
    (hPositive : ∀ s ∈ Set.Ioc (0 : ℝ) T, 0 < U s) :
    f (U T, a + j + c * T) =
      f (U 0, a) +
      (∫ s in 0..κ, fderiv ℝ f (U s, a + c * s) (1, 0) * deriv U s +
         c * fderiv ℝ f (U s, a + c * s) (0, 1)) +
      (f (U κ, a + j + c * κ) - f (U κ, a + c * κ)) +
      (∫ s in κ..T, fderiv ℝ f (U s, a + j + c * s) (1, 0) * deriv U s +
         c * fderiv ℝ f (U s, a + j + c * s) (0, 1)) := by
  sorry
