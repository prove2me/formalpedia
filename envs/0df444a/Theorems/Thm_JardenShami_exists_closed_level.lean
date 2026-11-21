-- Prove2me | Theorems.Thm_JardenShami_exists_closed_level
-- name    : JardenShami.exists_closed_level
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:37.468654+00:00
-- url     : https://prove2.me/theorems/f1a90fc5-8698-4088-9432-1464a7679f79
-- title:
--   Jarden Shami: exists closed level
-- statement:
--   AUX: not in paper. For regular `ρ < κ` (`κ` regular) and any `σ` mapping `κ` to `κ`, there
--   is a level `α ∈ (α₀, κ)` closed under `σ` such that any fewer than `ρ` ordinals below `α` are
--   bounded below `α` (`α` is the supremum of a `ρ`-sequence closing off under `σ`).
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L709-L777
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L709-L777

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.exists_closed_level {κ ρ : Cardinal.{w}} (hκ : κ.IsRegular) (hρ : ρ.IsRegular)
    (hρκ : ρ < κ) {α₀ : Ordinal.{w}} (hα₀ : α₀ < κ.ord) (σ : Ordinal.{w} → Ordinal.{w})
    (hσ : ∀ q < κ.ord, σ q < κ.ord) :
    ∃ α, α₀ < α ∧ α < κ.ord ∧ (∀ q < α, σ q < α) ∧
      ∀ (ι : Type w) (f : ι → Ordinal.{w}), #ι < ρ → (∀ i, f i < α) → ∃ q < α, ∀ i, f i ≤ q := by sorry
