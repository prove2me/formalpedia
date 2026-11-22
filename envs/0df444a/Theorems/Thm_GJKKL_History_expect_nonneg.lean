-- Prove2me | Theorems.Thm_GJKKL_History_expect_nonneg
-- name    : GJKKL.History.expect_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:54.5998+00:00
-- url     : https://prove2.me/theorems/9a0bb843-1f89-464d-b994-246799146625
-- title:
--   History: expect nonneg
-- statement:
--   The History construction uses the expect nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L109-L111
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L109-L111

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

theorem GJKKL.History.expect_nonneg {T : ℕ} {f : List α → ℝ} (hf : ∀ h, h.length = T → 0 ≤ f h) :
    0 ≤ expect κ T f := by sorry
