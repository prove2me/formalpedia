-- Prove2me | Theorems.Thm_List_sum_take_succ_getD
-- name    : List.sum_take_succ_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:15.643935+00:00
-- url     : https://prove2.me/theorems/c342436c-ad36-4d28-900c-2a64e9ea0092
-- title:
--   List: sum take succ get D
-- statement:
--   One more term of a partial sum; beyond the end of the list the term is `0`. Within the list,
--   `List.sum_take_succ` has `l[j]` in place of `l.getD j 0`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L200-L205
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L200-L205

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

theorem List.sum_take_succ_getD {M : Type*} [AddMonoid M] (l : List M) (j : ℕ) :
    (l.take (j + 1)).sum = (l.take j).sum + l.getD j 0 := by sorry
