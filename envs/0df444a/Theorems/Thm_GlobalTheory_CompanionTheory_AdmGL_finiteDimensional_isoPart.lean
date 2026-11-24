-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_finiteDimensional_isoPart
-- name    : GlobalTheory.CompanionTheory.AdmGL.finiteDimensional_isoPart
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:58:39.6778+00:00
-- url     : https://prove2.me/theorems/5f8e85cd-35e7-4353-a895-1c0f28be2b39
-- title:
--   Adm GL: finite Dimensional iso Part
-- statement:
--   The Adm GL construction uses the finite Dimensional iso Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteDimensionalIsoPartOfSimple.lean#L143-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteDimensionalIsoPartOfSimple.lean#L143-L165

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteDimensionalIsoPartOfSimple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdmGL
variable {K : Type} [Group K] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]

theorem GlobalTheory.CompanionTheory.AdmGL.finiteDimensional_isoPart {π : K →* (H →L[ℂ] H)} (hπ : ∀ k v, ‖π k v‖ = ‖v‖)
    (hadm : ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → (∀ k, ∀ w ∈ S, π k w ∈ S) →
      (∀ S' : Submodule ℂ H, S' ≤ S → (∀ k, ∀ w ∈ S', π k w ∈ S') → S' = ⊥ ∨ S' = S) →
      FiniteDimensional ℂ (sSup {S' | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧
        ∀ k, ∀ w ∈ S, T (π k w) = π k (T w)} : Submodule ℂ H))
    (d : ℕ) : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ K W),
      Module.finrank ℂ W = d → FiniteDimensional ℂ (isoPart π ρ) := by sorry
