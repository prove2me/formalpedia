-- Prove2me | Theorems.Thm_List_getD_set_of_lt
-- name    : List.getD_set_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:04.383486+00:00
-- url     : https://prove2.me/theorems/4839664c-28d4-491d-9706-08071f18d230
-- title:
--   List: get D set of lt
-- statement:
--   The entries of a list in which entry `q < l.length` was replaced by `a`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L81-L88
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L81-L88

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

theorem List.getD_set_of_lt {l : List α} {q : ℕ} (hq : q < l.length) (a d : α) (q' : ℕ) :
    (l.set q a).getD q' d = if q' = q then a else l.getD q' d := by sorry
