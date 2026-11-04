-- Prove2me | Theorems.Thm_List_abs_sum_take_map_le
-- name    : List.abs_sum_take_map_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:21.403879+00:00
-- url     : https://prove2.me/theorems/554af416-fe15-4f7a-a29c-33e20912e594
-- title:
--   List: abs sum take map le
-- statement:
--   If `|f x| ≤ B` for all `x ∈ l`, then every initial part of the numbers `f x` has a sum of
--   absolute value at most `l.length * B`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L246-L249
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L246-L249

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

theorem List.abs_sum_take_map_le (l : List α) (f : α → ℤ) {B : ℤ} (h : ∀ x ∈ l, |f x| ≤ B) (k : ℕ) :
    |((l.map f).take k).sum| ≤ l.length * B := by sorry
