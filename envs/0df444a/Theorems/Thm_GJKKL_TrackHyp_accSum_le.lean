-- Prove2me | Theorems.Thm_GJKKL_TrackHyp_accSum_le
-- name    : GJKKL.TrackHyp.accSum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:07.59058+00:00
-- url     : https://prove2.me/theorems/b4f9a535-c240-4836-80f1-e33193fdc838
-- title:
--   Track Hyp: acc Sum le
-- statement:
--   Accumulated variation of an affine frozen process along a good history.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L304-L320
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean#L304-L320

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

theorem GJKKL.TrackHyp.accSum_le (v : V) (σ : ℝ) (hσ : |σ| = 1) (φ : ℕ → ℝ)
    (hφ : ∀ t < T, |φ (t + 1) - φ t| ≤ (dh t - dh (t + 1)) + (δ (t + 1) - δ t)) :
    ∀ h : List (Finset V), h.length < T → AliveBefore (GoodState H dh δ) h →
      GoodState H dh δ h →
      accSum (greedyKernel H) (frozen H (fun t x => σ * x + φ t) v) h ≤
        ∑ t ∈ range (h.length + 1), bnd V k dh δ t
  := by sorry
