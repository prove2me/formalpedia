-- Prove2me | Theorems.Thm_List_mem_takeWhile_lt
-- name    : List.mem_takeWhile_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:36.861602+00:00
-- url     : https://prove2.me/theorems/bf5ab57a-0236-4934-b257-7923e5b7cf7c
-- title:
--   List: mem take While lt
-- statement:
--   The members below `b` at the beginning of a strictly increasing list are all its members
--   below `b`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L397-L403
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L397-L403

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

theorem List.mem_takeWhile_lt {b c : α} {l : List α} (h : l.Pairwise (· < ·)) :
    (c ∈ l.takeWhile fun c => c < b) ↔ c ∈ l ∧ c < b := by sorry
