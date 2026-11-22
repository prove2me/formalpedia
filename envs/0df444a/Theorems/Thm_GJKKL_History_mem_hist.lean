-- Prove2me | Theorems.Thm_GJKKL_History_mem_hist
-- name    : GJKKL.History.mem_hist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:30:02.668995+00:00
-- url     : https://prove2.me/theorems/d3b77cff-7871-43b2-abbd-bee82fbc15b9
-- title:
--   History: mem hist
-- statement:
--   The History construction uses the mem hist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L45-L51
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L45-L51

module
public import Mathlib
public import Definitions.Def_GJKKL_History_Basic
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem GJKKL.History.mem_hist {T : ℕ} {h : List α} : h ∈ hist α T ↔ h.length = T := by sorry
