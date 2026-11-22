-- Prove2me | Theorems.Thm_GJKKL_History_sum_hist_succ
-- name    : GJKKL.History.sum_hist_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:43.995684+00:00
-- url     : https://prove2.me/theorems/96ffe492-e800-45f5-9b43-e89cde1b4c74
-- title:
--   History: sum hist succ
-- statement:
--   The History construction uses the sum hist succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L53-L58
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L53-L58

module
public import Mathlib
public import Definitions.Def_GJKKL_History_Basic
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem GJKKL.History.sum_hist_succ (T : ℕ) (F : List α → ℝ) :
    ∑ h ∈ hist α (T + 1), F h = ∑ h ∈ hist α T, ∑ a, F (a :: h) := by sorry
