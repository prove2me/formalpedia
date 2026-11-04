-- Prove2me | Theorems.Thm_List_count_take_succ_getD
-- name    : List.count_take_succ_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:30.046004+00:00
-- url     : https://prove2.me/theorems/87550aaa-1b5d-4b39-9c0e-05ae4eae49c4
-- title:
--   List: count take succ get D
-- statement:
--   A count among the first `i + 1` entries, with entry `i` read by `getD`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L313-L316
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L313-L316

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

theorem List.count_take_succ_getD [DecidableEq α] (l : List α) (x : α) {i : ℕ} (hi : i < l.length)
    (d : α) :
    (l.take (i + 1)).count x = (l.take i).count x + if l.getD i d = x then 1 else 0 := by sorry
