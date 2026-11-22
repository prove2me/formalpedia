-- Prove2me | Theorems.Thm_GJKKL_TrackHyp_dv_bounds
-- name    : GJKKL.TrackHyp.dv_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:20.215185+00:00
-- url     : https://prove2.me/theorems/f6370834-437d-4afb-9be6-944a6151bb6c
-- title:
--   Track Hyp: dv bounds
-- statement:
--   The Track Hyp construction uses the dv bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L136-L140
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L136-L140

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

theorem GJKKL.TrackHyp.dv_bounds {h : List (Finset V)} (ht : Tracked H dh δ h) {v : V} (hv : v ∉ covered h) :
    dh h.length - δ h.length ≤ (dv H h v : ℝ) ∧ (dv H h v : ℝ) ≤ dh h.length + δ h.length := by sorry
