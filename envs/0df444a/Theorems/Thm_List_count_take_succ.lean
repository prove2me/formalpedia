-- Prove2me | Theorems.Thm_List_count_take_succ
-- name    : List.count_take_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:29.118584+00:00
-- url     : https://prove2.me/theorems/0b715216-c879-48fb-83d4-0b650a2467e9
-- title:
--   List: count take succ
-- statement:
--   A count among the first `i + 1` entries, from the count among the first `i` and entry `i`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L306-L310
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L306-L310

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

theorem List.count_take_succ [DecidableEq α] (l : List α) (x : α) {i : ℕ}
    (hi : i < l.length) :
    (l.take (i + 1)).count x = (l.take i).count x + if l[i] = x then 1 else 0 := by sorry
