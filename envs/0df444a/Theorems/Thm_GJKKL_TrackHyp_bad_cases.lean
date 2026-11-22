-- Prove2me | Theorems.Thm_GJKKL_TrackHyp_bad_cases
-- name    : GJKKL.TrackHyp.bad_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:54:13.618384+00:00
-- url     : https://prove2.me/theorems/9c84048d-b059-45b4-98ac-6c20ffc59d5e
-- title:
--   Track Hyp: bad cases
-- statement:
--   A first failure of a greedy history is a large deviation of some frozen process.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L355-L380
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L355-L380

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

theorem GJKKL.TrackHyp.bad_cases {h : List (Finset V)} (hT : h.length < T)
    (hal : AliveBefore (GoodState H dh δ) h) (hbad : ¬ GoodState H dh δ h) :
    ¬ IsGreedySeq H h ∨ ∃ v ∈ (univ : Finset V),
      (lam ≤ upperProc H dh δ v h - upperProc H dh δ v [] ∧ AliveBefore (GoodState H dh δ) h) ∨
      (lam ≤ lowerProc H dh δ v h - lowerProc H dh δ v [] ∧ AliveBefore (GoodState H dh δ) h) := by sorry
