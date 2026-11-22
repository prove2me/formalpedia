-- Prove2me | Theorems.Thm_GJKKL_increment_abs_le
-- name    : GJKKL.increment_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:43:57.243511+00:00
-- url     : https://prove2.me/theorems/54c6d90a-1b71-4d73-ab6f-80b867f03adf
-- title:
--   GJKKL: increment abs le
-- statement:
--   One step of an affine frozen process moves it by at most `k c + |Δφ|`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Increments.lean#L122-L143
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Increments.lean#L122-L143

module
public import Definitions.Def_GJKKL_Trajectory_Frozen
public import Definitions.Def_GJKKL_Trajectory_Trend
public import Definitions.Def_GJKKL_Trajectory_Increments
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset History Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem GJKKL.increment_abs_le (H : Finset (Finset V)) {k : ℕ} (hk : IsUniform H k) {c : ℕ}
    (hc : ∀ u w, u ≠ w → codegree H u w ≤ c) {v : V} {h : List (Finset V)} {a : Finset V}
    (ha : a ∈ avail H h) (σ : ℝ) (hσ : |σ| = 1) (φ : ℕ → ℝ) :
    |frozen H (fun t x => σ * x + φ t) v (a :: h) - frozen H (fun t x => σ * x + φ t) v h| ≤
      k * c + |φ (h.length + 1) - φ h.length| := by sorry
