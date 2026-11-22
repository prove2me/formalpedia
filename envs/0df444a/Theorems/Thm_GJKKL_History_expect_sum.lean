-- Prove2me | Theorems.Thm_GJKKL_History_expect_sum
-- name    : GJKKL.History.expect_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:49:07.713803+00:00
-- url     : https://prove2.me/theorems/79468ff9-3d52-4b69-af05-b30f6f9962a5
-- title:
--   History: expect sum
-- statement:
--   The History construction uses the expect sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L125-L129
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L125-L129

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

theorem GJKKL.History.expect_sum {ι : Type*} (s : Finset ι) (T : ℕ) (f : ι → List α → ℝ) :
    expect κ T (fun h => ∑ i ∈ s, f i h) = ∑ i ∈ s, expect κ T (f i) := by sorry
