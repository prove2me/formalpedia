-- Prove2me | Theorems.Thm_JardenShami_Tree_lt_iff_ht_lt_of_isChain
-- name    : JardenShami.Tree.lt_iff_ht_lt_of_isChain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:03.336787+00:00
-- url     : https://prove2.me/theorems/583bb32b-523e-4c2f-be98-79cf7ebd45b6
-- title:
--   Tree: lt iff ht lt of is Chain
-- statement:
--   AUX: not in paper. On a chain, `x < y` iff `ht x < ht y`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L165-L170
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L165-L170

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

theorem JardenShami.Tree.lt_iff_ht_lt_of_isChain {b : Set T} (hb : IsChain (· ≤ ·) b) {x y : T} (hx : x ∈ b)
    (hy : y ∈ b) : x < y ↔ ht x < ht y := by sorry
