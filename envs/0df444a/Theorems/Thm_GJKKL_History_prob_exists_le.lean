-- Prove2me | Theorems.Thm_GJKKL_History_prob_exists_le
-- name    : GJKKL.History.prob_exists_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:49:21.671826+00:00
-- url     : https://prove2.me/theorems/522c58ce-ed50-42d1-891e-445f44c90b33
-- title:
--   History: prob exists le
-- statement:
--   The union bound.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L189-L201
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L189-L201

module
public import Mathlib
public import Definitions.Def_GJKKL_History_Basic
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (κ : Kernel α)

theorem GJKKL.History.prob_exists_le {ι : Type*} (s : Finset ι) (T : ℕ) (P : ι → List α → Prop) :
    prob κ T (fun h => ∃ i ∈ s, P i h) ≤ ∑ i ∈ s, prob κ T (P i) := by sorry
