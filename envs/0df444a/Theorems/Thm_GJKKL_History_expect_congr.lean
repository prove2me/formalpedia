-- Prove2me | Theorems.Thm_GJKKL_History_expect_congr
-- name    : GJKKL.History.expect_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:55.693917+00:00
-- url     : https://prove2.me/theorems/afdba111-3372-421c-b01a-40519b74b5a6
-- title:
--   History: expect congr
-- statement:
--   The History construction uses the expect congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L105-L107
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L105-L107

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

theorem GJKKL.History.expect_congr {T : ℕ} {f g : List α → ℝ} (hfg : ∀ h, h.length = T → f h = g h) :
    expect κ T f = expect κ T g := by sorry
