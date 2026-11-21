-- Prove2me | Theorems.Thm_JardenShami_lt_of_le_of_le_of_ht_lt
-- name    : JardenShami.lt_of_le_of_le_of_ht_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:36.223805+00:00
-- url     : https://prove2.me/theorems/cc416216-a230-4018-82f6-346cda234104
-- title:
--   Jarden Shami: lt of le of le of ht lt
-- statement:
--   AUX: not in paper. A node of height `α` and a node of height `β > α` below a common node:
--   the first is below the second.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L793-L797
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L793-L797

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {T : Type w} [PartialOrder T] [IsTree T]

theorem JardenShami.lt_of_le_of_le_of_ht_lt {x y z : T} (hx : x ≤ z) (hy : y ≤ z) (h : ht x < ht y) :
    x < y := by sorry
