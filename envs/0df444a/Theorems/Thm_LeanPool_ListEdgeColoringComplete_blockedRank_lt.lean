-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_blockedRank_lt
-- name    : LeanPool.ListEdgeColoringComplete.blockedRank_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:00:57.266566+00:00
-- url     : https://prove2.me/theorems/70bc696b-d0e0-4bee-a541-3e29611016f1
-- title:
--   List Edge Coloring Complete: blocked Rank lt
-- statement:
--   The List Edge Coloring Complete construction uses the blocked Rank lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Basic.lean#L35-L38
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Basic.lean#L35-L38

module
public import Mathlib.Data.Fintype.Basic
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Basic
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete

theorem LeanPool.ListEdgeColoringComplete.blockedRank_lt (n i : ℕ) (hn : 2 ≤ n) (hi : i < n) :
    blockedRank n i < n := by sorry
