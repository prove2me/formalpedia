-- Prove2me | Theorems.Thm_GJKKL_History_expect_const_mul
-- name    : GJKKL.History.expect_const_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:36:47.847434+00:00
-- url     : https://prove2.me/theorems/215b441f-8683-4390-8250-710ecedf5e84
-- title:
--   History: expect const mul
-- statement:
--   The History construction uses the expect const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L119-L123
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L119-L123

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

theorem GJKKL.History.expect_const_mul (T : ℕ) (c : ℝ) (f : List α → ℝ) :
    expect κ T (fun h => c * f h) = c * expect κ T f := by sorry
