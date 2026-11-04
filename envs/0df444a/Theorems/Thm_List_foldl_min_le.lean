-- Prove2me | Theorems.Thm_List_foldl_min_le
-- name    : List.foldl_min_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:25.113209+00:00
-- url     : https://prove2.me/theorems/ca56e17a-89e0-43d2-abad-17d9e0dfddef
-- title:
--   List: foldl min le
-- statement:
--   A running minimum over `f 0, …, f m` is a lower bound of these values.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L281-L289
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L281-L289

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

theorem List.foldl_min_le [LinearOrder β] (f : ℕ → β) (m : ℕ) {k : ℕ} (hk : k ≤ m) :
    (List.range m).foldl (fun acc j => min acc (f (j + 1))) (f 0) ≤ f k := by sorry
