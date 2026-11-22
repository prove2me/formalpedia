-- Prove2me | Theorems.Thm_GJKKL_sum_K_mul_increment
-- name    : GJKKL.sum_K_mul_increment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:43:27.088151+00:00
-- url     : https://prove2.me/theorems/f65aa4d1-4b9a-4d51-9cd2-0e26998915cb
-- title:
--   GJKKL: sum K mul increment
-- statement:
--   The conditional expected increment of an affine frozen process, times `|A|`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Frozen.lean#L77-L116
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Frozen.lean#L77-L116

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

theorem GJKKL.sum_K_mul_increment (H : Finset (Finset V)) {v : V} {h : List (Finset V)}
    (hv : v ∉ covered h) (σ : ℝ) (φ : ℕ → ℝ) :
    ((avail H h).card : ℝ) * ∑ a, (greedyKernel H).K h a *
        (frozen H (fun t x => σ * x + φ t) v (a :: h) - frozen H (fun t x => σ * x + φ t) v h) =
      -σ * (lossSum H h v : ℝ) +
        ((avail H h \ Dv H h v).card : ℝ) * (φ (h.length + 1) - φ h.length) := by sorry
