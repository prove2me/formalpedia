-- Prove2me | Theorems.Thm_JardenShami_nonempty_iso_iff_treeOfColoring
-- name    : JardenShami.nonempty_iso_iff_treeOfColoring
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:45:07.111692+00:00
-- url     : https://prove2.me/theorems/470a532c-d147-4299-bdf9-2dfd592b5280
-- title:
--   Jarden Shami: nonempty iso iff tree Of Coloring
-- statement:
--   **Corollary 4.20** (Section 4). Let `T₁, T₂` be `κ`-trees without leaves and `e_i` an
--   enumeration of `T_i` that covers `T_i`. Then `T₁ ≅ T₂` iff `T(C(T₁,e₁)) ≅ T(C(T₂,e₂))`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L1149-L1164
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L1149-L1164

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.nonempty_iso_iff_treeOfColoring {κ : Cardinal.{w}}
    {T₁ T₂ : Type w} [PartialOrder T₁] [IsTree T₁] [PartialOrder T₂] [IsTree T₂]
    (h₁ : IsKappaTree κ T₁) (h₂ : IsKappaTree κ T₂)
    (hl₁ : ∀ t : T₁, ¬ IsLeaf t) (hl₂ : ∀ t : T₂, ¬ IsLeaf t)
    (e₁ : Enumeration κ T₁) (e₂ : Enumeration κ T₂) (c₁ : e₁.Covers) (c₂ : e₂.Covers)
    {C₁ : Coloring (Kappa κ) (Kappa (levelSup κ T₁))} (hC₁ : IsTreeColoring e₁ C₁)
    {C₂ : Coloring (Kappa κ) (Kappa (levelSup κ T₂))} (hC₂ : IsTreeColoring e₂ C₂) :
    Nonempty (T₁ ≃o T₂) ↔ Nonempty (treeOfColoring C₁ ≃o treeOfColoring C₂) := by sorry
