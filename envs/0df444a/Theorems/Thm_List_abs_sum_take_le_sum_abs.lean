-- Prove2me | Theorems.Thm_List_abs_sum_take_le_sum_abs
-- name    : List.abs_sum_take_le_sum_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:20.328444+00:00
-- url     : https://prove2.me/theorems/8a9ae840-63a7-47eb-beac-12474ceab8b7
-- title:
--   List: abs sum take le sum abs
-- statement:
--   The sum of an initial part of a list is at most the sum of the absolute values of the whole
--   list, in absolute value.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L235-L240
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L235-L240

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
variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]

theorem List.abs_sum_take_le_sum_abs (l : List R) (k : ℕ) :
    |(l.take k).sum| ≤ (l.map fun x => |x|).sum := by sorry
