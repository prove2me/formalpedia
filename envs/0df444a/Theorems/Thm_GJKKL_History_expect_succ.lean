-- Prove2me | Theorems.Thm_GJKKL_History_expect_succ
-- name    : GJKKL.History.expect_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:31:33.32315+00:00
-- url     : https://prove2.me/theorems/5621d1b5-0660-402c-9ede-f95fad9b0bcd
-- title:
--   History: expect succ
-- statement:
--   The tower property.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L91-L99
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L91-L99

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

theorem GJKKL.History.expect_succ (T : ℕ) (f : List α → ℝ) :
    expect κ (T + 1) f = expect κ T (fun h => ∑ a, κ.K h a * f (a :: h)) := by sorry
