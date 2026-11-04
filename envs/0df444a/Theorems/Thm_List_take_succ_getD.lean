-- Prove2me | Theorems.Thm_List_take_succ_getD
-- name    : List.take_succ_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:06.393866+00:00
-- url     : https://prove2.me/theorems/e923fed8-b4da-46ec-bfe2-32738726364c
-- title:
--   List: take succ get D
-- statement:
--   The first `i + 1` entries are the first `i` entries and entry `i`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L102-L105
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L102-L105

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

theorem List.take_succ_getD (l : List α) {i : ℕ} (hi : i < l.length) (d : α) :
    l.take (i + 1) = l.take i ++ [l.getD i d] := by sorry
