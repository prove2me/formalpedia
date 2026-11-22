-- Prove2me | Theorems.Thm_GJKKL_card_avail_bounds
-- name    : GJKKL.card_avail_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:52:55.503888+00:00
-- url     : https://prove2.me/theorems/fbef91b9-e2cc-4898-8bcf-c433e72c6b58
-- title:
--   GJKKL: card avail bounds
-- statement:
--   The GJKKL construction uses the card avail bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Increments.lean#L37-L59
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Increments.lean#L37-L59

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

theorem GJKKL.card_avail_bounds (H : Finset (Finset V)) {k : ℕ} (hk : IsUniform H k) (hk0 : 0 < k)
    {dh δ : ℕ → ℝ} {h : List (Finset V)} (hh : IsGreedySeq H h) (ht : Tracked H dh δ h) :
    ((Fintype.card V : ℝ) - k * h.length) / k * (dh h.length - δ h.length) ≤ (avail H h).card ∧
      ((avail H h).card : ℝ) ≤
        ((Fintype.card V : ℝ) - k * h.length) / k * (dh h.length + δ h.length) := by sorry
