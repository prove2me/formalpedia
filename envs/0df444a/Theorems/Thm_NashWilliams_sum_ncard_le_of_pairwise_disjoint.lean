-- Prove2me | Theorems.Thm_NashWilliams_sum_ncard_le_of_pairwise_disjoint
-- name    : NashWilliams.sum_ncard_le_of_pairwise_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:41:10.850854+00:00
-- url     : https://prove2.me/theorems/83dc4d32-97cd-4688-bd65-11ad3eee7f79
-- title:
--   Nash Williams: sum ncard le of pairwise disjoint
-- statement:
--   The sum of the sizes of pairwise disjoint subsets of a finite set is at most its size.
--
--   Source: https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L56-L62
-- source:
--   https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L56-L62

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux
set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph Function
open NashWilliams
variable {V : Type*}

theorem NashWilliams.sum_ncard_le_of_pairwise_disjoint {ι α : Type*} [Fintype ι] [Finite α] (A : ι → Set α)
    (B : Set α) (hAB : ∀ i, A i ⊆ B) (hd : Pairwise (Disjoint on A)) :
    ∑ i, (A i).ncard ≤ B.ncard := by sorry
