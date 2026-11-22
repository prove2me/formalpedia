-- Prove2me | Theorems.Thm_GJKKL_TrackHyp_card_sdiff_Dv
-- name    : GJKKL.TrackHyp.card_sdiff_Dv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:44:43.218829+00:00
-- url     : https://prove2.me/theorems/3f445f77-8756-45af-9180-b11d8334124a
-- title:
--   Track Hyp: card sdiff Dv
-- statement:
--   The Track Hyp construction uses the card sdiff Dv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L146-L150
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L146-L150

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

theorem GJKKL.TrackHyp.card_sdiff_Dv (h : List (Finset V)) (v : V) :
    ((avail H h \ Dv H h v).card : ℝ) = (avail H h).card - dv H h v := by sorry
