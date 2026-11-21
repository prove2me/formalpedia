-- Prove2me | Theorems.Thm_JardenShami_Tree_ht_injOn_of_isChain
-- name    : JardenShami.Tree.ht_injOn_of_isChain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:41.254186+00:00
-- url     : https://prove2.me/theorems/d2c14787-b3fb-4e46-9ef6-240ab9ab1ce8
-- title:
--   Tree: ht inj On of is Chain
-- statement:
--   AUX: not in paper. On a chain, the height is injective.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L173-L177
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L173-L177

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

theorem JardenShami.Tree.ht_injOn_of_isChain {b : Set T} (hb : IsChain (· ≤ ·) b) : Set.InjOn ht b := by sorry
