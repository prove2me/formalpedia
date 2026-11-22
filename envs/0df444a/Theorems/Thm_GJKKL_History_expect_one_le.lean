-- Prove2me | Theorems.Thm_GJKKL_History_expect_one_le
-- name    : GJKKL.History.expect_one_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:36:58.563873+00:00
-- url     : https://prove2.me/theorems/c42f44c2-c4b3-4d21-92f9-5d5f77eaa2a7
-- title:
--   History: expect one le
-- statement:
--   The total mass at time `T` is at most `1`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L144-L147
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L144-L147

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

theorem GJKKL.History.expect_one_le (T : ℕ) : expect κ T (fun _ => 1) ≤ 1 := by sorry
