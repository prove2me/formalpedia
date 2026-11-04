-- Prove2me | Theorems.Thm_List_sum_filter_finRange
-- name    : List.sum_filter_finRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:19.455411+00:00
-- url     : https://prove2.me/theorems/2a99bc17-345b-4d25-aa3c-15b058231792
-- title:
--   List: sum filter fin Range
-- statement:
--   A sum over the list of the indices with a property, as a sum over a finite set.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L220-L223
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L220-L223

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

theorem List.sum_filter_finRange {m : ℕ} (p : Fin m → Prop) [DecidablePred p] (F : Fin m → ℤ) :
    (((List.finRange m).filter fun x => p x).map F).sum = ∑ x ∈ Finset.univ.filter p, F x := by sorry
