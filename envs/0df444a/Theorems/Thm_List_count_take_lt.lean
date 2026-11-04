-- Prove2me | Theorems.Thm_List_count_take_lt
-- name    : List.count_take_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:29.198823+00:00
-- url     : https://prove2.me/theorems/a29b269a-64e4-448d-a8f3-1fe40d2db0d0
-- title:
--   List: count take lt
-- statement:
--   If entry `i < l.length` is `x`, then `x` occurs less often before place `i` than in the whole
--   list.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L320-L324
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L320-L324

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

theorem List.count_take_lt [DecidableEq α] {l : List α} {i : ℕ} {x : α} (hi : i < l.length) (d : α)
    (hx : l.getD i d = x) : (l.take i).count x < l.count x := by sorry
