-- Prove2me | Theorems.Thm_List_length_filter_range
-- name    : List.length_filter_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:31.351067+00:00
-- url     : https://prove2.me/theorems/4afec721-4ff4-4f5d-b02b-e56809e60309
-- title:
--   List: length filter range
-- statement:
--   The list of the `j < n` with `q j` has `Nat.count q n` members.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L339-L341
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L339-L341

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

theorem List.length_filter_range (q : ℕ → Prop) [DecidablePred q] (n : ℕ) :
    ((List.range n).filter fun j => decide (q j)).length = Nat.count q n := by sorry
