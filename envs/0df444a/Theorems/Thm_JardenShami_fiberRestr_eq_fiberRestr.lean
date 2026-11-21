-- Prove2me | Theorems.Thm_JardenShami_fiberRestr_eq_fiberRestr
-- name    : JardenShami.fiberRestr_eq_fiberRestr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:39.80967+00:00
-- url     : https://prove2.me/theorems/84244822-c079-4d1d-a0c6-2bd4f7cd0b5a
-- title:
--   Jarden Shami: fiber Restr eq fiber Restr
-- statement:
--   AUX: not in paper. Equality of the graphs `C(·,δ) ↾ β`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L229-L235
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L229-L235

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

theorem JardenShami.fiberRestr_eq_fiberRestr {C : Coloring (Kappa κ) D} {δ₁ β₁ δ₂ β₂ : Kappa κ}
    (h₁ : β₁ ≤ δ₁) (h₂ : β₂ ≤ δ₂) (hβ : β₁ = β₂)
    (hc : ∀ (α : Kappa κ) (hα₁ : α < β₁) (hα₂ : α < β₂),
      C.color α δ₁ (hα₁.trans_le h₁) = C.color α δ₂ (hα₂.trans_le h₂)) :
    fiberRestr C δ₁ β₁ h₁ = fiberRestr C δ₂ β₂ h₂ := by sorry
