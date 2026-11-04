-- Prove2me | Theorems.Thm_List_length_flatMap_finRange
-- name    : List.length_flatMap_finRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:10.303198+00:00
-- url     : https://prove2.me/theorems/bb9c0266-54a1-4b00-a0f5-2cf16fb2eb90
-- title:
--   List: length flat Map fin Range
-- statement:
--   The length of `n` blocks of length `k`, numbered by `Fin n`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L135-L137
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L135-L137

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

theorem List.length_flatMap_finRange {n k : ℕ} (f : Fin n → List α) (hf : ∀ i, (f i).length = k) :
    ((List.finRange n).flatMap f).length = n * k := by sorry
