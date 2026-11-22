-- Prove2me | Theorems.Thm_GJKKL_TrackHyp_K1_nonneg
-- name    : GJKKL.TrackHyp.K1_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:44.933118+00:00
-- url     : https://prove2.me/theorems/4f348689-157c-4486-baf7-b7c3b5179754
-- title:
--   Track Hyp: K1 nonneg
-- statement:
--   The Track Hyp construction uses the K1 nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L107-L109
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L107-L109

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

theorem GJKKL.TrackHyp.K1_nonneg : (0 : ℝ) ≤ (k : ℝ) - 1 := by sorry
