-- Prove2me | Theorems.Thm_GJKKL_TrackHyp_condAbsInc_le
-- name    : GJKKL.TrackHyp.condAbsInc_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:53:44.774813+00:00
-- url     : https://prove2.me/theorems/e022ea12-56bb-44f5-b3f8-2a67883adb5f
-- title:
--   Track Hyp: cond Abs Inc le
-- statement:
--   The conditional absolute increment of an affine frozen process at a good state.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L256-L301
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L256-L301

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

theorem GJKKL.TrackHyp.condAbsInc_le {h : List (Finset V)} (hT : h.length < T) (hg : GoodState H dh δ h)
    (v : V) (σ : ℝ) (hσ : |σ| = 1) (φ : ℕ → ℝ)
    (hφ : |φ (h.length + 1) - φ h.length| ≤
      (dh h.length - dh (h.length + 1)) + (δ (h.length + 1) - δ h.length)) :
    condAbsInc (greedyKernel H) (frozen H (fun t x => σ * x + φ t) v) h ≤
      bnd V k dh δ h.length := by sorry
