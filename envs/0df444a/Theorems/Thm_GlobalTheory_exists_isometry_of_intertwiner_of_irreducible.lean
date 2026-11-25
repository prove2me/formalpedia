-- Prove2me | Theorems.Thm_GlobalTheory_exists_isometry_of_intertwiner_of_irreducible
-- name    : GlobalTheory.exists_isometry_of_intertwiner_of_irreducible
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:33:34.629072+00:00
-- url     : https://prove2.me/theorems/f30a7795-f321-4c1e-9cca-071f52d26752
-- title:
--   Global Theory: exists isometry of intertwiner of irreducible
-- statement:
--   The Global Theory construction uses the exists isometry of intertwiner of irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsIsometryOfIntertwinerOfIrreducible.lean#L7-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsIsometryOfIntertwinerOfIrreducible.lean#L7-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsIsometryOfIntertwinerOfIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped InnerProductSpace

theorem GlobalTheory.exists_isometry_of_intertwiner_of_irreducible
    (V₁ : Type) [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁] [FiniteDimensional ℂ V₁]
    (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] [FiniteDimensional ℂ V₂]
    (ι : Type) (π₁ : ι → (V₁ →L[ℂ] V₁)) (π₂ : ι → (V₂ →L[ℂ] V₂)) (T : V₁ ≃ₗ[ℂ] V₂)
    (h₁ : ∀ i v, ‖π₁ i v‖ = ‖v‖) (h₂ : ∀ i v, ‖π₂ i v‖ = ‖v‖)
    (hirr : ∀ S : Submodule ℂ V₁, (∀ i, ∀ v ∈ S, π₁ i v ∈ S) → S = ⊥ ∨ S = ⊤)
    (hT : ∀ i v, T (π₁ i v) = π₂ i (T v)) :
    ∃ φ : V₁ ≃ₗᵢ[ℂ] V₂, ∀ i v, φ (π₁ i v) = π₂ i (φ v) := by sorry
