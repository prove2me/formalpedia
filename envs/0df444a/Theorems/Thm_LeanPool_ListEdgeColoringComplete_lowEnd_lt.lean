-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_lowEnd_lt
-- name    : LeanPool.ListEdgeColoringComplete.lowEnd_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:08:26.847423+00:00
-- url     : https://prove2.me/theorems/ef2cd20e-e118-4834-9a66-1f5fe2de4f6b
-- title:
--   List Edge Coloring Complete: low End lt
-- statement:
--   The List Edge Coloring Complete construction uses the low End lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Certificate.lean#L107-L109
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Certificate.lean#L107-L109

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

theorem LeanPool.ListEdgeColoringComplete.lowEnd_lt (hu : u < n) (hv : v < n) : lowEnd n u v < n := by sorry
