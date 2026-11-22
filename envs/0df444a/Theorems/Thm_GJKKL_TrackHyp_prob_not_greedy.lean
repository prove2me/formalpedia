-- Prove2me | Theorems.Thm_GJKKL_TrackHyp_prob_not_greedy
-- name    : GJKKL.TrackHyp.prob_not_greedy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:54:05.683284+00:00
-- url     : https://prove2.me/theorems/735e86b4-15b7-4e21-a7da-113c090fb08d
-- title:
--   Track Hyp: prob not greedy
-- statement:
--   The Track Hyp construction uses the prob not greedy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L382-L389
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L382-L389

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

theorem GJKKL.TrackHyp.prob_not_greedy (i : ℕ) :
    prob (greedyKernel H) i (fun h => ¬ IsGreedySeq H h) = 0 := by sorry
