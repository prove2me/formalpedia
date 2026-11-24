-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharacterTrivial_eq_one_of_isFundamentalDomain
-- name    : GlobalTheory.CompanionTheory.SW.CharacterTrivial.eq_one_of_isFundamentalDomain
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:02:14.064801+00:00
-- url     : https://prove2.me/theorems/19a4a70e-cbbe-4d25-87dc-f740b612b963
-- title:
--   Character Trivial: eq one of is Fundamental Domain
-- statement:
--   The Character Trivial construction uses the eq one of is Fundamental Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ModularCharacterTrivialFiniteCovolume.lean#L9-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ModularCharacterTrivialFiniteCovolume.lean#L9-L101

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteCovolumeUnimodular
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_QuotientMeasureTower
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ModularCharacterTrivialFiniteCovolume
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.CharacterTrivial

theorem GlobalTheory.CompanionTheory.SW.CharacterTrivial.eq_one_of_isFundamentalDomain :
    ∀ (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
      [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁]
      (Γ₁ : Subgroup G₁) [Countable Γ₁] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (𝓕₁ : Set G₁),
      IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → μ₁ 𝓕₁ < ⊤ → ∀ δ : G₁ →* ℝ≥0, Measurable δ →
        (∀ γ ∈ Γ₁, δ γ = 1) → ∀ u, δ u = 1 := by sorry
