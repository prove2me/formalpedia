-- Prove2me | Theorems.Thm_List_length_filter_lt_succ
-- name    : List.length_filter_lt_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:31.106927+00:00
-- url     : https://prove2.me/theorems/bf569a8b-c659-4dab-aa4a-c083123d255a
-- title:
--   List: length filter lt succ
-- statement:
--   The members with `t a < z + 1` are those with `t a < z` and those with `t a = z`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L327-L336
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L327-L336

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

theorem List.length_filter_lt_succ (t : α → ℕ) (z : ℕ) (l : List α) :
    (l.filter fun a => decide (t a < z + 1)).length =
      (l.filter fun a => decide (t a < z)).length +
        (l.filter fun a => decide (t a = z)).length := by sorry
