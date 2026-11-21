-- Prove2me | Theorems.Thm_JardenShami_ht_fiberRestr
-- name    : JardenShami.ht_fiberRestr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:09.437363+00:00
-- url     : https://prove2.me/theorems/377a9630-45a9-4f7f-8429-a1ff6be2f25d
-- title:
--   Jarden Shami: ht fiber Restr
-- statement:
--   AUX: not in paper. The height of `C(·,δ) ↾ β` in `T(C)` is `β`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L253-L280
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L253-L280

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

theorem JardenShami.ht_fiberRestr (C : Coloring (Kappa κ) D) {δ β : Kappa κ} (h : β ≤ δ) :
    ht (⟨fiberRestr C δ β h, δ, β, h, rfl⟩ : treeOfColoring C) = (β : Ordinal.{w}) := by sorry
