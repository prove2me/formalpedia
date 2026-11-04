-- Prove2me | Theorems.Thm_List_length_flatMap_le
-- name    : List.length_flatMap_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:13.937081+00:00
-- url     : https://prove2.me/theorems/0249890d-91cc-4090-a76b-823b1264ca0b
-- title:
--   List: length flat Map le
-- statement:
--   Blocks of length at most `c`, one for each member of `l`, have length at most `l.length * c`
--   in all.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L178-L181
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L178-L181

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

theorem List.length_flatMap_le (l : List α) (f : α → List β) (c : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ c) : (l.flatMap f).length ≤ l.length * c := by sorry
