-- Prove2me | Theorems.Thm_GJKKL_TrackHyp_avail_nonempty
-- name    : GJKKL.TrackHyp.avail_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:53:13.781815+00:00
-- url     : https://prove2.me/theorems/43ca5d0e-0c0d-4bf6-b623-1f4cc853482d
-- title:
--   Track Hyp: avail nonempty
-- statement:
--   At a time `< T`, a tracked greedy state has an available edge.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L117-L123
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L117-L123

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

theorem GJKKL.TrackHyp.avail_nonempty {h : List (Finset V)} (hT : h.length < T) (hh : IsGreedySeq H h)
    (ht : Tracked H dh δ h) : (avail H h).Nonempty := by sorry
