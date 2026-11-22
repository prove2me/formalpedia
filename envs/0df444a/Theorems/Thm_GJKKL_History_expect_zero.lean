-- Prove2me | Theorems.Thm_GJKKL_History_expect_zero
-- name    : GJKKL.History.expect_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:30:06.295801+00:00
-- url     : https://prove2.me/theorems/742dca7f-b060-4fcd-a023-c6c272569433
-- title:
--   History: expect zero
-- statement:
--   The History construction uses the expect zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L87-L88
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L87-L88

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

theorem GJKKL.History.expect_zero (f : List α → ℝ) : expect κ 0 f = f [] := by sorry
