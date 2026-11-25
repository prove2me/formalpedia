-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_localRank_injective
-- name    : LeanPool.ListEdgeColoringComplete.localRank_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:08:08.566015+00:00
-- url     : https://prove2.me/theorems/fa6ce08d-c9eb-41c9-8e4f-09fa19a4f68f
-- title:
--   List Edge Coloring Complete: local Rank injective
-- statement:
--   Distinct edges of `C_u` receive distinct ranks.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Certificate.lean#L146-L150
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Certificate.lean#L146-L150

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

theorem LeanPool.ListEdgeColoringComplete.localRank_injective (hu : u < n) (hv : v < n) (hw : w < n) (huv : u ≠ v)
    (huw : u ≠ w) (h : localRank n u v = localRank n u w) : v = w := by sorry
