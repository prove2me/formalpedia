-- Prove2me | Theorems.Thm_List_getD_append_singleton
-- name    : List.getD_append_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:05.593145+00:00
-- url     : https://prove2.me/theorems/194d3728-b34e-4108-beb4-f1618c4a4e30
-- title:
--   List: get D append singleton
-- statement:
--   One more member at the end changes the entry number `l.length` only.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L91-L99
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L91-L99

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

theorem List.getD_append_singleton (l : List α) (a d : α) :
    (fun e => (l ++ [a]).getD e d) = Function.update (fun e => l.getD e d) l.length a := by sorry
