-- Prove2me | Theorems.Thm_GJKKL_TrackHyp_inc_upperProc
-- name    : GJKKL.TrackHyp.inc_upperProc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:53:35.399368+00:00
-- url     : https://prove2.me/theorems/4bd6fa2f-e895-4e6f-9606-521e21502769
-- title:
--   Track Hyp: inc upper Proc
-- statement:
--   The Track Hyp construction uses the inc upper Proc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L218-L230
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L218-L230

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

theorem GJKKL.TrackHyp.inc_upperProc {h : List (Finset V)} (hT : h.length < T) (v : V) {a : Finset V}
    (ha : (greedyKernel H).K h a ≠ 0) :
    |upperProc H dh δ v (a :: h) - upperProc H dh δ v h| ≤ C := by sorry
