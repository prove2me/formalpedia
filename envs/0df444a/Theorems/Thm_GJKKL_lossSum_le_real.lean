-- Prove2me | Theorems.Thm_GJKKL_lossSum_le_real
-- name    : GJKKL.lossSum_le_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:44:03.586349+00:00
-- url     : https://prove2.me/theorems/c63f3f65-1899-4350-9afa-da46228358f2
-- title:
--   GJKKL: loss Sum le real
-- statement:
--   The GJKKL construction uses the loss Sum le real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Increments.lean#L108-L119
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Increments.lean#L108-L119

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

theorem GJKKL.lossSum_le_real (H : Finset (Finset V)) {k : ℕ} (hk : IsUniform H k)
    {dh δ : ℕ → ℝ} {h : List (Finset V)} (ht : Tracked H dh δ h) (v : V) {c : ℕ}
    (hc : ∀ u w, u ≠ w → codegree H u w ≤ c) :
    (lossSum H h v : ℝ) ≤ (dv H h v : ℝ) * ((k : ℝ) - 1) * (dh h.length + δ h.length) := by sorry
