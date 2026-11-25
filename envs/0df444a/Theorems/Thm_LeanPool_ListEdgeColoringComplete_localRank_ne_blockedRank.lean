-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_localRank_ne_blockedRank
-- name    : LeanPool.ListEdgeColoringComplete.localRank_ne_blockedRank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:08:07.141966+00:00
-- url     : https://prove2.me/theorems/53f40085-95da-4f5f-9a66-d4d8f158e991
-- title:
--   List Edge Coloring Complete: local Rank ne blocked Rank
-- statement:
--   No actual edge of `C_u` receives the blocked rank.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Certificate.lean#L140-L143
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Certificate.lean#L140-L143

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

theorem LeanPool.ListEdgeColoringComplete.localRank_ne_blockedRank (hu : u < n) (hv : v < n) (huv : u ≠ v) :
    localRank n u v ≠ blockedRank n u := by sorry
