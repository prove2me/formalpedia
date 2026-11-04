-- Prove2me | Theorems.Thm_List_getD_map_range
-- name    : List.getD_map_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:03.380922+00:00
-- url     : https://prove2.me/theorems/099bdb25-c2c9-4014-8286-09b24b2fa776
-- title:
--   List: get D map range
-- statement:
--   Entry `i < n` of the table `f 0, …, f (n - 1)`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L68-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L68-L71

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

theorem List.getD_map_range (f : ℕ → α) {n i : ℕ} (hi : i < n) (d : α) :
    ((List.range n).map f).getD i d = f i := by sorry
