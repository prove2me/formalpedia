-- Prove2me | Theorems.Thm_GJKKL_History_stopped_cons_of_not_alive
-- name    : GJKKL.History.stopped_cons_of_not_alive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:49:44.435662+00:00
-- url     : https://prove2.me/theorems/d83e51ee-bf02-49ed-9b45-59e8ad8c710b
-- title:
--   History: stopped cons of not alive
-- statement:
--   The History construction uses the stopped cons of not alive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Freedman.lean#L122-L124
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Freedman.lean#L122-L124

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

theorem GJKKL.History.stopped_cons_of_not_alive {a : α} {h : List α} (hal : ¬ AliveBefore G (a :: h)) :
    stopped X G (a :: h) = stopped X G h := by sorry
