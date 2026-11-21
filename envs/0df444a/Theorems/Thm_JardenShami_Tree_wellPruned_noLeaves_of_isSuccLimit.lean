-- Prove2me | Theorems.Thm_JardenShami_Tree_wellPruned_noLeaves_of_isSuccLimit
-- name    : JardenShami.Tree.wellPruned_noLeaves_of_isSuccLimit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:40.469636+00:00
-- url     : https://prove2.me/theorems/caee4e8d-cf8a-4d86-884e-716d1a52f9da
-- title:
--   Tree: well Pruned no Leaves of is Succ Limit
-- statement:
--   **Section 4, preliminaries** (unnumbered, "Clearly"). Every well-pruned tree of limit
--   ordinal height has no leaves.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L233-L238
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L233-L238

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open JardenShami.Tree
variable {T : Type w} [PartialOrder T] [IsTree T]

theorem JardenShami.Tree.wellPruned_noLeaves_of_isSuccLimit (hT : WellPruned T)
    (hlim : Order.IsSuccLimit (height T)) : ∀ t : T, ¬ IsLeaf t := by sorry
