-- Prove2me | Theorems.Thm_List_exists_foldl_min_eq
-- name    : List.exists_foldl_min_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:28.139399+00:00
-- url     : https://prove2.me/theorems/f882f24e-22f0-40aa-9fbf-59ba076d710b
-- title:
--   List: exists foldl min eq
-- statement:
--   A running minimum over `f 0, …, f m` is one of these values.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L292-L301
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L292-L301

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

theorem List.exists_foldl_min_eq [LinearOrder β] (f : ℕ → β) (m : ℕ) :
    ∃ k ≤ m, (List.range m).foldl (fun acc j => min acc (f (j + 1))) (f 0) = f k := by sorry
