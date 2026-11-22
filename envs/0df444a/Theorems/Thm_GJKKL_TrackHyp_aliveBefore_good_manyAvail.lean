-- Prove2me | Theorems.Thm_GJKKL_TrackHyp_aliveBefore_good_manyAvail
-- name    : GJKKL.TrackHyp.aliveBefore_good_manyAvail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:54:16.869887+00:00
-- url     : https://prove2.me/theorems/89a25958-fd32-4d94-a0c5-cd3aeb25f2ff
-- title:
--   Track Hyp: alive Before good many Avail
-- statement:
--   On the good event, at least `aP(t)(dh(t) - δ(t))` edges were available at every past
--   time `t`: the event `T*` of the counting step.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L431-L436
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L431-L436

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

theorem GJKKL.TrackHyp.aliveBefore_good_manyAvail :
    ∀ h : List (Finset V), AliveBefore (GoodState H dh δ) h →
      ManyAvail H (fun t => aPar V k t * (dh t - δ t)) h
  := by sorry
