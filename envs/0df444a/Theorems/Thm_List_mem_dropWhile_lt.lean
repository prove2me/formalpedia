-- Prove2me | Theorems.Thm_List_mem_dropWhile_lt
-- name    : List.mem_dropWhile_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:35.733059+00:00
-- url     : https://prove2.me/theorems/9261f9df-bd53-4f9f-848c-564a7ad040e4
-- title:
--   List: mem drop While lt
-- statement:
--   What remains of a strictly increasing list after the members below `a` are skipped.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L387-L393
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L387-L393

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

theorem List.mem_dropWhile_lt {a c : α} {l : List α} (h : l.Pairwise (· < ·)) :
    (c ∈ l.dropWhile fun c => c < a) ↔ c ∈ l ∧ a ≤ c := by sorry
