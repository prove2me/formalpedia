-- Prove2me | Theorems.Thm_GJKKL_History_aliveBefore_cons
-- name    : GJKKL.History.aliveBefore_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:32:22.898799+00:00
-- url     : https://prove2.me/theorems/5e48758c-d503-467b-ad72-dd46bb1da6d5
-- title:
--   History: alive Before cons
-- statement:
--   The History construction uses the alive Before cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Freedman.lean#L90-L91
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Freedman.lean#L90-L91

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

theorem GJKKL.History.aliveBefore_cons (G : List α → Prop) (a : α) (h : List α) :
    AliveBefore G (a :: h) ↔ AliveBefore G h ∧ G h := by sorry
