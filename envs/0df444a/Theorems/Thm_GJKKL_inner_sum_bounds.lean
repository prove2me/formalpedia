-- Prove2me | Theorems.Thm_GJKKL_inner_sum_bounds
-- name    : GJKKL.inner_sum_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:43:53.802477+00:00
-- url     : https://prove2.me/theorems/c566124c-39a0-4ff8-b24b-d9aeeaef2ffb
-- title:
--   GJKKL: inner sum bounds
-- statement:
--   The GJKKL construction uses the inner sum bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Increments.lean#L66-L85
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Increments.lean#L66-L85

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

theorem GJKKL.inner_sum_bounds (H : Finset (Finset V)) {k : ℕ} (hk : IsUniform H k)
    {dh δ : ℕ → ℝ} {h : List (Finset V)} (ht : Tracked H dh δ h) {v : V} {f : Finset V}
    (hf : f ∈ Dv H h v) :
    ((k : ℝ) - 1) * (dh h.length - δ h.length) ≤ ∑ u ∈ f.erase v, (dv H h u : ℝ) ∧
      ∑ u ∈ f.erase v, (dv H h u : ℝ) ≤ ((k : ℝ) - 1) * (dh h.length + δ h.length) := by sorry
