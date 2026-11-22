-- Prove2me | Theorems.Thm_GJKKL_History_expect_add
-- name    : GJKKL.History.expect_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:36:43.425497+00:00
-- url     : https://prove2.me/theorems/856beb1c-9ab6-4228-8413-63ce94eecec3
-- title:
--   History: expect add
-- statement:
--   The History construction uses the expect add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L113-L117
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L113-L117

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

theorem GJKKL.History.expect_add (T : ℕ) (f g : List α → ℝ) :
    expect κ T (fun h => f h + g h) = expect κ T f + expect κ T g := by sorry
