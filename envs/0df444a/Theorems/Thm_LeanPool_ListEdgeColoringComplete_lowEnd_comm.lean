-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_lowEnd_comm
-- name    : LeanPool.ListEdgeColoringComplete.lowEnd_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:08:23.228953+00:00
-- url     : https://prove2.me/theorems/f78d1458-639b-408c-9b1b-2af133289193
-- title:
--   List Edge Coloring Complete: low End comm
-- statement:
--   The List Edge Coloring Complete construction uses the low End comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Certificate.lean#L102-L105
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Certificate.lean#L102-L105

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Fin
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Certificate
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
variable {n u v w : ℕ}

theorem LeanPool.ListEdgeColoringComplete.lowEnd_comm (n u v : ℕ) :
    lowEnd n u v = lowEnd n v u := by sorry
