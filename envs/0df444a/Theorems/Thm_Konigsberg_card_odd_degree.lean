-- Prove2me | Theorems.Thm_Konigsberg_card_odd_degree
-- name    : Konigsberg.card_odd_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:34:32.420536+00:00
-- url     : https://prove2.me/theorems/d62a343b-a1fb-5bea-b990-ede3ea474b27
-- title:
--   Konigsberg: card odd degree
-- statement:
--   The Konigsberg construction uses the card odd degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Konigsberg.lean#L52-L53
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Konigsberg.lean#L52-L53

module
public import Definitions.Def_Euler_Basic
public import Mathlib.Tactic.FinCases
public import Definitions.Def_Euler_Konigsberg
set_option autoImplicit true
@[expose] public section
public section
open Konigsberg

theorem Konigsberg.card_odd_degree : Fintype.card {v : Fin 11 | Odd (graph.degree v)} = 4 := by sorry
