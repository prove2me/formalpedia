-- Prove2me | Theorems.Thm_GJKKL_History_expect_mono
-- name    : GJKKL.History.expect_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:30:18.451042+00:00
-- url     : https://prove2.me/theorems/20777269-a4e9-4504-8dda-f9b6b7ca8e0d
-- title:
--   History: expect mono
-- statement:
--   The History construction uses the expect mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L101-L103
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L101-L103

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

theorem GJKKL.History.expect_mono {T : ℕ} {f g : List α → ℝ} (hfg : ∀ h, h.length = T → f h ≤ g h) :
    expect κ T f ≤ expect κ T g := by sorry
