-- Prove2me | Theorems.Thm_List_getD_map_of_lt
-- name    : List.getD_map_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:05.05548+00:00
-- url     : https://prove2.me/theorems/06255731-0440-4d7b-b16e-4aef448c25e9
-- title:
--   List: get D map of lt
-- statement:
--   Entry `i < l.length` of `l.map f`, whatever the two defaults. Mathlib's `List.getD_map` is for
--   all `i`, with the default `f d`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L75-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L75-L78

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

theorem List.getD_map_of_lt (f : α → β) {l : List α} {i : ℕ} (hi : i < l.length) (d : α) (d' : β) :
    (l.map f).getD i d' = f (l.getD i d) := by sorry
