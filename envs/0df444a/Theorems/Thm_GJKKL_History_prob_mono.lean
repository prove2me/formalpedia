-- Prove2me | Theorems.Thm_GJKKL_History_prob_mono
-- name    : GJKKL.History.prob_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:37:05.110427+00:00
-- url     : https://prove2.me/theorems/df65ad9c-fe0c-45b5-9389-6d6954db4912
-- title:
--   History: prob mono
-- statement:
--   The History construction uses the prob mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L171-L178
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L171-L178

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

theorem GJKKL.History.prob_mono {T : ℕ} {P Q : List α → Prop} (hPQ : ∀ h, h.length = T → P h → Q h) :
    prob κ T P ≤ prob κ T Q := by sorry
