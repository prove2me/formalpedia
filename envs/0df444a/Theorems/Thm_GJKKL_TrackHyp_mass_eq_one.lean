-- Prove2me | Theorems.Thm_GJKKL_TrackHyp_mass_eq_one
-- name    : GJKKL.TrackHyp.mass_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:53:14.4749+00:00
-- url     : https://prove2.me/theorems/088d6ca2-a164-421c-af95-4435490cb314
-- title:
--   Track Hyp: mass eq one
-- statement:
--   The Track Hyp construction uses the mass eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L125-L127
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L125-L127

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

theorem GJKKL.TrackHyp.mass_eq_one {h : List (Finset V)} (hg : GoodState H dh δ h) :
    ∑ a, (greedyKernel H).K h a = 1 := by sorry
