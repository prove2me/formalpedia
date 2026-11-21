-- Prove2me | Theorems.Thm_JardenShami_fiberRestr_ssubset_iff
-- name    : JardenShami.fiberRestr_ssubset_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:07.754771+00:00
-- url     : https://prove2.me/theorems/5542b3dc-ea0c-450a-829d-48267694448d
-- title:
--   Jarden Shami: fiber Restr ssubset iff
-- statement:
--   AUX: not in paper. Strict inclusion between the graphs `C(·,δ) ↾ β`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L238-L250
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L238-L250

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

theorem JardenShami.fiberRestr_ssubset_iff {C : Coloring (Kappa κ) D} {δ₁ β₁ δ₂ β₂ : Kappa κ}
    (h₁ : β₁ ≤ δ₁) (h₂ : β₂ ≤ δ₂) :
    fiberRestr C δ₁ β₁ h₁ ⊂ fiberRestr C δ₂ β₂ h₂ ↔
      β₁ < β₂ ∧ ∀ (α : Kappa κ) (hα₁ : α < β₁) (hα₂ : α < β₂),
        C.color α δ₁ (hα₁.trans_le h₁) = C.color α δ₂ (hα₂.trans_le h₂) := by sorry
