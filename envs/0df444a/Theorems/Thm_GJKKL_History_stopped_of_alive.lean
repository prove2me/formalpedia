-- Prove2me | Theorems.Thm_GJKKL_History_stopped_of_alive
-- name    : GJKKL.History.stopped_of_alive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:49:36.251384+00:00
-- url     : https://prove2.me/theorems/89811ca4-1fe7-4100-ab4f-57d48d2d490d
-- title:
--   History: stopped of alive
-- statement:
--   The History construction uses the stopped of alive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Freedman.lean#L118-L120
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Freedman.lean#L118-L120

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Definitions.Def_GJKKL_History_Freedman
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (κ : Kernel α) (X : List α → ℝ) (G : List α → Prop)

theorem GJKKL.History.stopped_of_alive : ∀ {h : List α}, AliveBefore G h → stopped X G h = X h
  := by sorry
