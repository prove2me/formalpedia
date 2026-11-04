-- Prove2me | Theorems.Thm_List_sum_flatMap_map
-- name    : List.sum_flatMap_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:18.339161+00:00
-- url     : https://prove2.me/theorems/168e2389-65d0-4e8b-be61-64c4d1e3dfca
-- title:
--   List: sum flat Map map
-- statement:
--   A sum over a concatenation of lists is the sum of the sums over the lists.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L213-L217
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L213-L217

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

theorem List.sum_flatMap_map {α β : Type*} (l : List α) (g : α → List β) (F : β → ℤ) :
    ((l.flatMap g).map F).sum = (l.map fun x => ((g x).map F).sum).sum := by sorry
