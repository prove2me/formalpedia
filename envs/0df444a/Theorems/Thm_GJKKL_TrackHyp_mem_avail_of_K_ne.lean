-- Prove2me | Theorems.Thm_GJKKL_TrackHyp_mem_avail_of_K_ne
-- name    : GJKKL.TrackHyp.mem_avail_of_K_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:44:40.399998+00:00
-- url     : https://prove2.me/theorems/b3af76c7-8569-4915-b769-b0cf756154bd
-- title:
--   Track Hyp: mem avail of K ne
-- statement:
--   The Track Hyp construction uses the mem avail of K ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L214-L216
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L214-L216

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

theorem GJKKL.TrackHyp.mem_avail_of_K_ne {h : List (Finset V)} {a : Finset V}
    (ha : (greedyKernel H).K h a ≠ 0) : a ∈ avail H h := by sorry
