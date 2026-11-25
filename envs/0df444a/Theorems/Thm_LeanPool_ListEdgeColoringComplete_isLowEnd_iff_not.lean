-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_isLowEnd_iff_not
-- name    : LeanPool.ListEdgeColoringComplete.isLowEnd_iff_not
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:08:19.729795+00:00
-- url     : https://prove2.me/theorems/1d536f4b-9e7b-4e75-bd0d-15763bc519d2
-- title:
--   List Edge Coloring Complete: is Low End iff not
-- statement:
--   The List Edge Coloring Complete construction uses the is Low End iff not property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Certificate.lean#L97-L100
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Certificate.lean#L97-L100

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

theorem LeanPool.ListEdgeColoringComplete.isLowEnd_iff_not (hv : v < n) (huv : u ≠ v) :
    IsLowEnd n u v ↔ ¬ IsLowEnd n v u := by sorry
