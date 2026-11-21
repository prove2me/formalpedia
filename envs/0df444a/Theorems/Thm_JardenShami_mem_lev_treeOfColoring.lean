-- Prove2me | Theorems.Thm_JardenShami_mem_lev_treeOfColoring
-- name    : JardenShami.mem_lev_treeOfColoring
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:52.283622+00:00
-- url     : https://prove2.me/theorems/0bab4a68-7158-4f87-b8ec-56cf219610f7
-- title:
--   Jarden Shami: mem lev tree Of Coloring
-- statement:
--   AUX: not in paper. The nodes of `Lev_α(T(C))` are the graphs `C(·,δ) ↾ β` with `β = α`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L283-L295
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L283-L295

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {D : Type w}

theorem JardenShami.mem_lev_treeOfColoring {C : Coloring (Kappa κ) D} {g : treeOfColoring C}
    {α : Ordinal.{w}} :
    g ∈ Lev (treeOfColoring C) α ↔
      ∃ (δ β : Kappa κ) (h : β ≤ δ), g.1 = fiberRestr C δ β h ∧ (β : Ordinal.{w}) = α := by sorry
