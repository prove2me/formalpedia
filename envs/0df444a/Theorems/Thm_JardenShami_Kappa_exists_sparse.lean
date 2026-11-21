-- Prove2me | Theorems.Thm_JardenShami_Kappa_exists_sparse
-- name    : JardenShami.Kappa.exists_sparse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:00.929882+00:00
-- url     : https://prove2.me/theorems/bb82aed7-4ef8-4f18-a51a-117b74b4630f
-- title:
--   Kappa: exists sparse
-- statement:
--   AUX: not in paper. For regular `κ`, a `κ`-sized `Γ ⊆ κ` and `F : κ → κ`, there is a
--   `κ`-sized `Γ' ⊆ Γ` such that `F γ₀ < γ` for all `γ₀ < γ` in `Γ'`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L109-L129
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L109-L129

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}}

theorem JardenShami.Kappa.exists_sparse (hκ : κ.IsRegular) {Γ : Set (Kappa κ)} (hΓ : #Γ = κ)
    (F : Kappa κ → Kappa κ) :
    ∃ Γ' ⊆ Γ, #Γ' = κ ∧ ∀ γ₀ ∈ Γ', ∀ γ ∈ Γ', γ₀ < γ → F γ₀ < γ := by sorry
