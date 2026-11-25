-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_fullRank_injective
-- name    : LeanPool.ListEdgeColoringComplete.fullRank_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:14:59.221865+00:00
-- url     : https://prove2.me/theorems/1895a5c5-0de2-4cbd-9691-5bff627eec0b
-- title:
--   List Edge Coloring Complete: full Rank injective
-- statement:
--   The List Edge Coloring Complete construction uses the full Rank injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Certificate.lean#L159-L166
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Certificate.lean#L159-L166

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

theorem LeanPool.ListEdgeColoringComplete.fullRank_injective (hu : u < n) (hv : v < n) (hw : w < n)
    (h : fullRank n u v = fullRank n u w) : v = w := by sorry
