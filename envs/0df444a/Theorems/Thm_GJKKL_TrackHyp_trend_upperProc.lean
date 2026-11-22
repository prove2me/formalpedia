-- Prove2me | Theorems.Thm_GJKKL_TrackHyp_trend_upperProc
-- name    : GJKKL.TrackHyp.trend_upperProc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:53:37.015855+00:00
-- url     : https://prove2.me/theorems/e055f7e0-f0a3-4de7-a88b-61caac81ae4b
-- title:
--   Track Hyp: trend upper Proc
-- statement:
--   Trend of the upper process.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L153-L180
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L153-L180

module
public import Definitions.Def_GJKKL_Trajectory_Increments
public import Definitions.Def_GJKKL_History_FirstFailure
public import Definitions.Def_GJKKL_Greedy_Counting
public import Definitions.Def_GJKKL_Trajectory_Tracking
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset History Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
open GJKKL.TrackHyp
variable {H : Finset (Finset V)} {k c : ℕ} {dh δ : ℕ → ℝ} {T : ℕ} {B lam C s : ℝ}
  (hyp : TrackHyp H k c dh δ T B lam C s)
include hyp

theorem GJKKL.TrackHyp.trend_upperProc {h : List (Finset V)} (hT : h.length < T) (hg : GoodState H dh δ h)
    (v : V) :
    ∑ a, (greedyKernel H).K h a * (upperProc H dh δ v (a :: h) - upperProc H dh δ v h) ≤ 0 := by sorry
