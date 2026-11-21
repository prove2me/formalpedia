-- Prove2me | Theorems.Thm_JardenShami_Tree_ht_le_ht_of_le
-- name    : JardenShami.Tree.ht_le_ht_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:35.720513+00:00
-- url     : https://prove2.me/theorems/4e0773b9-fa65-42eb-b572-5166dcdac49b
-- title:
--   Tree: ht le ht of le
-- statement:
--   AUX: not in paper. Heights are monotone.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L144-L145
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L144-L145

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

theorem JardenShami.Tree.ht_le_ht_of_le {s t : T} (h : s ≤ t) : ht s ≤ ht t := by sorry
