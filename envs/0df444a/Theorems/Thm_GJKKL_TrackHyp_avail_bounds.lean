-- Prove2me | Theorems.Thm_GJKKL_TrackHyp_avail_bounds
-- name    : GJKKL.TrackHyp.avail_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:52.179328+00:00
-- url     : https://prove2.me/theorems/e460f0e6-8359-4de5-baa3-d161cc362cc9
-- title:
--   Track Hyp: avail bounds
-- statement:
--   The Track Hyp construction uses the avail bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L111-L114
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L111-L114

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

theorem GJKKL.TrackHyp.avail_bounds {h : List (Finset V)} (hh : IsGreedySeq H h) (ht : Tracked H dh δ h) :
    aPar V k h.length * (dh h.length - δ h.length) ≤ (avail H h).card ∧
      ((avail H h).card : ℝ) ≤ aPar V k h.length * (dh h.length + δ h.length) := by sorry
