-- Prove2me | Theorems.Thm_GJKKL_sum_K_mul_abs_increment_le
-- name    : GJKKL.sum_K_mul_abs_increment_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:52:56.747839+00:00
-- url     : https://prove2.me/theorems/eb0cba5d-212d-449d-8cd2-9f3c5bcee2f2
-- title:
--   GJKKL: sum K mul abs increment le
-- statement:
--   The conditional expected absolute increment of an affine frozen process, times `|A|`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Frozen.lean#L119-L161
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Frozen.lean#L119-L161

module
public import Definitions.Def_GJKKL_Greedy_Drift
public import Definitions.Def_GJKKL_History_Freedman
public import Definitions.Def_GJKKL_Trajectory_Frozen
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset History
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem GJKKL.sum_K_mul_abs_increment_le (H : Finset (Finset V)) {v : V} {h : List (Finset V)}
    (hv : v ∉ covered h) (σ : ℝ) (hσ : |σ| = 1) (φ : ℕ → ℝ) :
    ((avail H h).card : ℝ) * ∑ a, (greedyKernel H).K h a *
        |frozen H (fun t x => σ * x + φ t) v (a :: h) - frozen H (fun t x => σ * x + φ t) v h| ≤
      (lossSum H h v : ℝ) + ((avail H h).card : ℝ) * |φ (h.length + 1) - φ h.length| := by sorry
