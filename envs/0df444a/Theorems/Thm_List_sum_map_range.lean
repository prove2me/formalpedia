-- Prove2me | Theorems.Thm_List_sum_map_range
-- name    : List.sum_map_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:14.592472+00:00
-- url     : https://prove2.me/theorems/7b439d76-2db1-4773-a31d-188d1e013366
-- title:
--   List: sum map range
-- statement:
--   The sum of the table `f 0, …, f (n - 1)` is the sum over `Finset.range n`. For a sum over
--   `Fin n` go on with `Finset.sum_range`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L187-L189
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L187-L189

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

theorem List.sum_map_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by sorry
