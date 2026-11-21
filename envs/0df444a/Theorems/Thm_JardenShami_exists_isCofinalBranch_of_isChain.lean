-- Prove2me | Theorems.Thm_JardenShami_exists_isCofinalBranch_of_isChain
-- name    : JardenShami.exists_isCofinalBranch_of_isChain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:39.622122+00:00
-- url     : https://prove2.me/theorems/1cc387d4-3e4d-460f-9b77-136e007285f7
-- title:
--   Jarden Shami: exists is Cofinal Branch of is Chain
-- statement:
--   AUX: not in paper. In a `κ`-tree, a chain of size `≥ κ` yields a cofinal branch.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L848-L853
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L848-L853

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.exists_isCofinalBranch_of_isChain {κ : Cardinal.{w}} {T : Type w} [PartialOrder T]
    [IsTree T] (hT : IsKappaTree κ T) {c : Set T} (hc : IsChain (· ≤ ·) c) (hcκ : κ ≤ #c) :
    ∃ b : Set T, IsCofinalBranch b := by sorry
