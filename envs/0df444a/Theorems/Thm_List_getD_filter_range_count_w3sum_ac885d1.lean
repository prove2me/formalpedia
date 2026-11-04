-- Prove2me | Theorems.Thm_List_getD_filter_range_count_w3sum_ac885d1
-- name    : List.getD_filter_range_count_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:05.013244+00:00
-- url     : https://prove2.me/theorems/957eb652-6566-4f6d-b5c1-b3d3bd4fc8fc
-- title:
--   List: get D filter range count
-- statement:
--   In the increasing list of the `j < n` with `q j`, the member `i` has the number
--   `Nat.count q i`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L345-L359
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L345-L359

module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Count
public import Definitions.Def_Submission_ThreeSumApsp_Util_List
set_option autoImplicit false
public section
open List
variable {α β : Type*}

theorem List.getD_filter_range_count_w3sum_ac885d1 (q : ℕ → Prop) [DecidablePred q] (n : ℕ) {i : ℕ}
    (hi : i < n) (hq : q i) :
    ((List.range n).filter fun j => decide (q j)).getD (Nat.count q i) 0 = i := by sorry
