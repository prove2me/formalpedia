-- Prove2me | Theorems.Thm_JardenShami_nonempty_iso_iff_historyTree
-- name    : JardenShami.nonempty_iso_iff_historyTree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:43:41.104181+00:00
-- url     : https://prove2.me/theorems/934b9d3d-c38b-434e-826e-192cfee098b7
-- title:
--   Jarden Shami: nonempty iso iff history Tree
-- statement:
--   **Corollary 4.5** (Section 4, `\label{corollary reconstruction a tree from its history}`).
--   Two trees without leaves are isomorphic iff their history trees are isomorphic.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L473-L514
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L473-L514

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {T : Type w} [PartialOrder T] [IsTree T]

theorem JardenShami.nonempty_iso_iff_historyTree {S : Type w} [PartialOrder S] [IsTree S]
    (hT : ∀ t : T, ¬ IsLeaf t) (hS : ∀ s : S, ¬ IsLeaf s) :
    Nonempty (T ≃o S) ↔ Nonempty (HistoryTree T ≃o HistoryTree S) := by sorry
