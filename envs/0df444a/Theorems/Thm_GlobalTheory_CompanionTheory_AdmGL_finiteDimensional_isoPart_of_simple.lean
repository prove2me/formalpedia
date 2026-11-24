-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_finiteDimensional_isoPart_of_simple
-- name    : GlobalTheory.CompanionTheory.AdmGL.finiteDimensional_isoPart_of_simple
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:16:42.706884+00:00
-- url     : https://prove2.me/theorems/7b68a96a-ba11-401a-a654-3512cea408d5
-- title:
--   Adm GL: finite Dimensional iso Part of simple
-- statement:
--   The Adm GL construction uses the finite Dimensional iso Part of simple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteDimensionalIsoPartOfSimple.lean#L78-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteDimensionalIsoPartOfSimple.lean#L78-L141

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

theorem GlobalTheory.CompanionTheory.AdmGL.finiteDimensional_isoPart_of_simple {π : K →* (H →L[ℂ] H)}
    (hadm : ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → (∀ k, ∀ w ∈ S, π k w ∈ S) →
      (∀ S' : Submodule ℂ H, S' ≤ S → (∀ k, ∀ w ∈ S', π k w ∈ S') → S' = ⊥ ∨ S' = S) →
      FiniteDimensional ℂ (sSup {S' | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧
        ∀ k, ∀ w ∈ S, T (π k w) = π k (T w)} : Submodule ℂ H))
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ K W)
    (hs : ∀ W' : Submodule ℂ W, (∀ k, W' ≤ W'.comap (ρ k)) → W' = ⊥ ∨ W' = ⊤) :
    FiniteDimensional ℂ (isoPart π ρ) := by sorry
