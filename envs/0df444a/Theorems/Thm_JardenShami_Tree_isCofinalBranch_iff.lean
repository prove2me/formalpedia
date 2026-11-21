-- Prove2me | Theorems.Thm_JardenShami_Tree_isCofinalBranch_iff
-- name    : JardenShami.Tree.isCofinalBranch_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:07.986172+00:00
-- url     : https://prove2.me/theorems/866dbefd-6e90-4c21-b2a9-55a3584f1a27
-- title:
--   Tree: is Cofinal Branch iff
-- statement:
--   AUX: not in paper. In a tree of height `κ`, a branch is cofinal iff it has size `κ`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L200-L220
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L200-L220

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
open JardenShami.Tree
variable {T : Type w} [PartialOrder T] [IsTree T]

theorem JardenShami.Tree.isCofinalBranch_iff {κ : Cardinal.{w}} (hT : height T = κ.ord) {b : Set T} :
    IsCofinalBranch b ↔ IsBranch b ∧ #b = κ := by sorry
