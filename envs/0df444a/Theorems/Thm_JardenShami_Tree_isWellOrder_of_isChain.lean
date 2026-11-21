-- Prove2me | Theorems.Thm_JardenShami_Tree_isWellOrder_of_isChain
-- name    : JardenShami.Tree.isWellOrder_of_isChain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:07.940017+00:00
-- url     : https://prove2.me/theorems/70a4e2c5-1783-4c99-a06c-7a87e4ce56fa
-- title:
--   Tree: is Well Order of is Chain
-- statement:
--   AUX: not in paper. A chain of a tree is well-ordered.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L180-L186
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L180-L186

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

theorem JardenShami.Tree.isWellOrder_of_isChain {b : Set T} (hb : IsChain (· ≤ ·) b) :
    IsWellOrder b (fun x y => (x : T) < y) := by sorry
