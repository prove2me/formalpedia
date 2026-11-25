-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_localRank_add
-- name    : LeanPool.ListEdgeColoringComplete.localRank_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:08:02.78187+00:00
-- url     : https://prove2.me/theorems/37208641-6ecf-4e67-9f5f-198caf2f88d7
-- title:
--   List Edge Coloring Complete: local Rank add
-- statement:
--   The two local ranks of an edge add up to the target degree `ρ`.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Certificate.lean#L130-L133
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Certificate.lean#L130-L133

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

theorem LeanPool.ListEdgeColoringComplete.localRank_add (hu : u < n) (hv : v < n) (huv : u ≠ v) :
    localRank n u v + localRank n v u = targetDegree n u v := by sorry
