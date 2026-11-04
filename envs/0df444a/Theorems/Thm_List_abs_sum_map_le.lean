-- Prove2me | Theorems.Thm_List_abs_sum_map_le
-- name    : List.abs_sum_map_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:23.042647+00:00
-- url     : https://prove2.me/theorems/967f1435-39ea-4903-a301-def5f75871b3
-- title:
--   List: abs sum map le
-- statement:
--   If `|f x| ≤ B` for all `x ∈ l`, then `|(l.map f).sum| ≤ l.length * B`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L252-L255
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L252-L255

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

theorem List.abs_sum_map_le (l : List α) (f : α → ℤ) {B : ℤ} (h : ∀ x ∈ l, |f x| ≤ B) :
    |(l.map f).sum| ≤ l.length * B := by sorry
