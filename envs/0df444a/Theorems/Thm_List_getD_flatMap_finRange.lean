-- Prove2me | Theorems.Thm_List_getD_flatMap_finRange
-- name    : List.getD_flatMap_finRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:12.978503+00:00
-- url     : https://prove2.me/theorems/807f618d-5d32-400d-ae5b-980172079dae
-- title:
--   List: get D flat Map fin Range
-- statement:
--   Blocks of length `k`, numbered by `Fin n`: entry `r` of block `i` has the index `i * k + r`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L140-L148
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L140-L148

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

theorem List.getD_flatMap_finRange {n k : ℕ} (f : Fin n → List α) (hf : ∀ i, (f i).length = k)
    (i : Fin n) {r : ℕ} (hr : r < k) (d : α) :
    ((List.finRange n).flatMap f).getD ((i : ℕ) * k + r) d = (f i).getD r d := by sorry
