-- Prove2me | Theorems.Thm_JardenShami_treeOfColoring_downwardClosed
-- name    : JardenShami.treeOfColoring_downwardClosed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:52.07162+00:00
-- url     : https://prove2.me/theorems/3096e192-f750-45df-a8ce-0565515b22bf
-- title:
--   Jarden Shami: tree Of Coloring downward Closed
-- statement:
--   **Definition 4.6** (Section 4), implicit claim: `T(C)` is downward closed in
--   `(^{<κ}D, ⊆)`, i.e. closed under restriction to an initial segment `{α : α < γ}`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L633-L643
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L633-L643

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {D : Type v}

theorem JardenShami.treeOfColoring_downwardClosed (C : Coloring (Kappa κ) D) :
    ∀ g ∈ treeOfColoring C, ∀ γ : Kappa κ, {p ∈ g | p.1 < γ} ∈ treeOfColoring C := by sorry
