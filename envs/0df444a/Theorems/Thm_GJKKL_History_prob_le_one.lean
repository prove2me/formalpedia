-- Prove2me | Theorems.Thm_GJKKL_History_prob_le_one
-- name    : GJKKL.History.prob_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:02:16.520082+00:00
-- url     : https://prove2.me/theorems/51a92853-7b18-44ee-9908-6dddad029213
-- title:
--   History: prob le one
-- statement:
--   The History construction uses the prob le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L165-L169
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L165-L169

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

theorem GJKKL.History.prob_le_one (T : ℕ) (P : List α → Prop) : prob κ T P ≤ 1 := by sorry
