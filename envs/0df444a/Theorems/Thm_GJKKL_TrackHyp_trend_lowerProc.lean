-- Prove2me | Theorems.Thm_GJKKL_TrackHyp_trend_lowerProc
-- name    : GJKKL.TrackHyp.trend_lowerProc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:53:30.930746+00:00
-- url     : https://prove2.me/theorems/3ad7135b-ed0d-422d-a227-6bcf457aeced
-- title:
--   Track Hyp: trend lower Proc
-- statement:
--   Trend of the lower process.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L183-L212
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L183-L212

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

theorem GJKKL.TrackHyp.trend_lowerProc {h : List (Finset V)} (hT : h.length < T) (hg : GoodState H dh δ h)
    (v : V) :
    ∑ a, (greedyKernel H).K h a * (lowerProc H dh δ v (a :: h) - lowerProc H dh δ v h) ≤ 0 := by sorry
