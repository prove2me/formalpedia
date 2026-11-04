-- Prove2me | Theorems.Thm_List_sum_take_map_range_succ
-- name    : List.sum_take_map_range_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:19.103198+00:00
-- url     : https://prove2.me/theorems/99e17613-d925-4a9d-8a4e-f24a50855725
-- title:
--   List: sum take map range succ
-- statement:
--   One more term of a partial sum of the table `f 0, …, f (n - 1)`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L208-L210
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L208-L210

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

theorem List.sum_take_map_range_succ {M : Type*} [AddMonoid M] (f : ℕ → M) {n j : ℕ} (hj : j < n) :
    (((List.range n).map f).take (j + 1)).sum = (((List.range n).map f).take j).sum + f j := by sorry
