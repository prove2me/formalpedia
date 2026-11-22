-- Prove2me | Theorems.Thm_GJKKL_TrackHyp_freedman_lowerProc
-- name    : GJKKL.TrackHyp.freedman_lowerProc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:53:55.732819+00:00
-- url     : https://prove2.me/theorems/e43ecaf8-c759-443e-be3e-401ec74b4308
-- title:
--   Track Hyp: freedman lower Proc
-- statement:
--   The Track Hyp construction uses the freedman lower Proc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L338-L352
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L338-L352

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

theorem GJKKL.TrackHyp.freedman_lowerProc (v : V) {i : ℕ} (hi : i ≤ T) :
    prob (greedyKernel H) i (fun h => lam ≤ lowerProc H dh δ v h - lowerProc H dh δ v [] ∧
      AliveBefore (GoodState H dh δ) h) ≤ Real.exp (-(lam ^ 2 / (2 * C * (lam + s)))) := by sorry
