-- Prove2me | Theorems.Thm_JardenShami_exists_wellPruned_subtree
-- name    : JardenShami.exists_wellPruned_subtree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:45:48.230494+00:00
-- url     : https://prove2.me/theorems/9bca5d66-1577-49be-9c5a-3edf251585bd
-- title:
--   Jarden Shami: exists well Pruned subtree
-- statement:
--   AUX: not in paper. In the proof of Claim 7.8, Case A, the paper calls this a well-known fact
--   ("it a well-known fact that every `κ`-tree has a well-pruned subtree which is a `κ`-tree") and
--   does not prove it. Stated for regular `κ`, the only case used (Claim 7.8 assumes `κ` regular); for
--   singular `κ` it can fail. A subtree is a subset with the induced order.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L483-L487
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L483-L487

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.exists_wellPruned_subtree (κ : Cardinal.{w}) (hκ : κ.IsRegular)
    (T : Type w) [PartialOrder T] [IsTree T] (hT : IsKappaTree κ T) :
    ∃ S : Set T, IsKappaTree κ S ∧ WellPruned S := by sorry
