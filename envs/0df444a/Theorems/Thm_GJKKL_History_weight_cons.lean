-- Prove2me | Theorems.Thm_GJKKL_History_weight_cons
-- name    : GJKKL.History.weight_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:30:03.310461+00:00
-- url     : https://prove2.me/theorems/069a42bd-11e9-446e-a16c-7bedd947fd28
-- title:
--   History: weight cons
-- statement:
--   The History construction uses the weight cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L77-L78
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L77-L78

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

theorem GJKKL.History.weight_cons (a : α) (h : List α) : weight κ (a :: h) = weight κ h * κ.K h a := by sorry

attribute [defeq] GJKKL.History.weight_cons
