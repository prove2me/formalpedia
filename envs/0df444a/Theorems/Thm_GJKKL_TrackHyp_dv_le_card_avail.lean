-- Prove2me | Theorems.Thm_GJKKL_TrackHyp_dv_le_card_avail
-- name    : GJKKL.TrackHyp.dv_le_card_avail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:53:22.41181+00:00
-- url     : https://prove2.me/theorems/a3947e7b-11f8-4f66-bd36-2ac2092f5406
-- title:
--   Track Hyp: dv le card avail
-- statement:
--   The Track Hyp construction uses the dv le card avail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L142-L144
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L142-L144

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

theorem GJKKL.TrackHyp.dv_le_card_avail (h : List (Finset V)) (v : V) :
    (dv H h v : ℝ) ≤ (avail H h).card := by sorry
