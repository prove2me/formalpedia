-- Prove2me | Theorems.Thm_JardenShami_Tree_ht_lt_height
-- name    : JardenShami.Tree.ht_lt_height
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:36.344106+00:00
-- url     : https://prove2.me/theorems/c9e51d1c-e145-4ab8-a515-f918cc4ccd3e
-- title:
--   Tree: ht lt height
-- statement:
--   AUX: not in paper. Every node has height smaller than the height of the tree.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L199-L210
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L199-L210

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

theorem JardenShami.Tree.ht_lt_height (t : T) : ht t < height T := by sorry
