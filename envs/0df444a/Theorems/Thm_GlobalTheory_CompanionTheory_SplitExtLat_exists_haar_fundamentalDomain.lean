-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SplitExtLat_exists_haar_fundamentalDomain
-- name    : GlobalTheory.CompanionTheory.SplitExtLat.exists_haar_fundamentalDomain
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:16:11.219167+00:00
-- url     : https://prove2.me/theorems/58c39a42-3b22-4c99-ab9f-a10b8854e5fa
-- title:
--   Split Ext Lat: exists haar fundamental Domain
-- statement:
--   The Split Ext Lat construction uses the exists haar fundamental Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SplitExtensionFundamentalDomain.lean#L16-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SplitExtensionFundamentalDomain.lean#L16-L38

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SplitHomeoApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicFundamentalDomainSplitStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ModularCharacterTrivialFiniteCovolumeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicHaarDecompositionStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicQuotientMeasureStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicFundamentalDomainVolumeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicIntegralUnfoldingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicLeviIntegralFormulaStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SplitExtensionFundamentalDomain
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SplitExtLat

theorem GlobalTheory.CompanionTheory.SplitExtLat.exists_haar_fundamentalDomain : ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁), Continuous ι → Continuous π → (∀ u, π (ι u) = u) → ∀ (Γ : Subgroup P) (Γ₁ : Subgroup G₁) [Countable Γ] [Countable Γ₁], (∃ U ∈ 𝓝 (1 : P), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → (∀ u ∈ Γ₁, ι u ∈ Γ) → (∀ γ ∈ Γ, π γ ∈ Γ₁) → ∀ (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (𝓕₁ : Set G₁), IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → μ₁ 𝓕₁ < ⊤ → (∃ K : Set P, IsCompact K ∧ ∀ m ∈ π.ker, ∃ γ ∈ Γ, π γ = 1 ∧ γ * m ∈ K) → ∃ (ν : Measure π.ker) (𝓕N : Set π.ker) (μP : Measure P) (𝓕P : Set P), ν.IsHaarMeasure ∧ IsFundamentalDomain (Γ.subgroupOf π.ker) 𝓕N ν ∧ ν 𝓕N ≠ 0 ∧ ν 𝓕N < ⊤ ∧ μP.IsHaarMeasure ∧ IsFundamentalDomain Γ 𝓕P μP ∧ μP 𝓕P < ⊤ ∧ ∀ f : P → ℝ≥0∞, Measurable f → ∫⁻ p in 𝓕P, f p ∂μP = ∫⁻ u in 𝓕₁, ∫⁻ m in 𝓕N, f ((m : P) * ι u) ∂ν ∂μ₁ := by sorry
