-- Prove2me | Theorems.Thm_Konigsberg_degrees
-- name    : Konigsberg.degrees
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:43:56.574312+00:00
-- url     : https://prove2.me/theorems/3131ad72-c82c-4681-956a-f7f4cc7f5a3e
-- title:
--   Konigsberg: degrees
-- statement:
--   The Konigsberg construction uses the degrees property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Konigsberg.lean#L48-L50
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Konigsberg.lean#L48-L50

module
public import Definitions.Def_Euler_Basic
public import Mathlib.Tactic.FinCases
public import Definitions.Def_Euler_Konigsberg
set_option autoImplicit true
@[expose] public section
public section
open Konigsberg

theorem Konigsberg.degrees :
    graph.degree 0 = 5 ∧ graph.degree 1 = 3 ∧ graph.degree 2 = 3 ∧ graph.degree 3 = 3 := by sorry
