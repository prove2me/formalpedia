-- Prove2me | Theorems.Thm_List_getD_take_of_lt
-- name    : List.getD_take_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:07.636191+00:00
-- url     : https://prove2.me/theorems/5399553f-b95f-4be3-bac2-c5dfd3b35081
-- title:
--   List: get D take of lt
-- statement:
--   Entry `j < n` of the first `n` entries.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L63-L65
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L63-L65

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

theorem List.getD_take_of_lt (l : List α) {n j : ℕ} (hj : j < n) (d : α) :
    (l.take n).getD j d = l.getD j d := by sorry
