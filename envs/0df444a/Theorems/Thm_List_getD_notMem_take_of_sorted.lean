-- Prove2me | Theorems.Thm_List_getD_notMem_take_of_sorted
-- name    : List.getD_notMem_take_of_sorted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:37.688565+00:00
-- url     : https://prove2.me/theorems/94f02a9d-d776-4c1c-b712-214c0d2fae07
-- title:
--   List: get D not Mem take of sorted
-- statement:
--   In a weakly increasing list, an entry that is the first or differs from its predecessor has not
--   occurred before.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L407-L423
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L407-L423

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
variable [LinearOrder α]

theorem List.getD_notMem_take_of_sorted {l : List α} (hs : l.Pairwise (· ≤ ·)) {i : ℕ}
    (hi : i < l.length)
    (d : α) (h : i = 0 ∨ l.getD i d ≠ l.getD (i - 1) d) : l.getD i d ∉ l.take i := by sorry
