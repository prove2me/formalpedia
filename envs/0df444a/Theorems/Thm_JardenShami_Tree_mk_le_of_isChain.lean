-- Prove2me | Theorems.Thm_JardenShami_Tree_mk_le_of_isChain
-- name    : JardenShami.Tree.mk_le_of_isChain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:48.83586+00:00
-- url     : https://prove2.me/theorems/7320bd32-b6f3-4065-86b0-3dabb878474a
-- title:
--   Tree: mk le of is Chain
-- statement:
--   AUX: not in paper. In a tree of height `κ`, every chain has size `≤ κ`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L189-L197
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L189-L197

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

theorem JardenShami.Tree.mk_le_of_isChain {κ : Cardinal.{w}} (hT : height T = κ.ord) {b : Set T}
    (hb : IsChain (· ≤ ·) b) : #b ≤ κ := by sorry
