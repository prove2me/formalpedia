-- Prove2me | Theorems.Thm_JardenShami_exists_wellPruned_subtree_downward
-- name    : JardenShami.exists_wellPruned_subtree_downward
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:43:21.395486+00:00
-- url     : https://prove2.me/theorems/7c35c756-00ec-422c-b777-04a5b4ca5e72
-- title:
--   Jarden Shami: exists well Pruned subtree downward
-- statement:
--   AUX: not in paper. Strong form of `exists_wellPruned_subtree`: for regular `κ`, every
--   `κ`-tree has a downward closed subset (so heights are the same as in `T`) which is a well-pruned
--   `κ`-tree: the nodes above a fixed root `r` that have `κ` nodes above them.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L409-L475
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L409-L475

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree
variable {T : Type w} [PartialOrder T] [IsTree T]

theorem JardenShami.exists_wellPruned_subtree_downward (κ : Cardinal.{w}) (hκ : κ.IsRegular)
    (T : Type w) [PartialOrder T] [IsTree T] (hT : IsKappaTree κ T) :
    ∃ S : Set T, (∀ s ∈ S, ∀ t < s, t ∈ S) ∧ IsKappaTree κ S ∧ WellPruned S := by sorry
