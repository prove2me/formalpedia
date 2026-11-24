-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SplitExtLat_ae_exists_smul_mem_image_prod
-- name    : GlobalTheory.CompanionTheory.SplitExtLat.ae_exists_smul_mem_image_prod
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:14:49.15825+00:00
-- url     : https://prove2.me/theorems/c2a4545c-ee46-4137-8a49-c00dd56213dc
-- title:
--   Split Ext Lat: ae exists smul mem image prod
-- statement:
--   The Split Ext Lat construction uses the ae exists smul mem image prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ParabolicFundamentalDomainVolume.lean#L8-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ParabolicFundamentalDomainVolume.lean#L8-L26

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SplitHomeoApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicFundamentalDomainVolume
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

theorem GlobalTheory.CompanionTheory.SplitExtLat.ae_exists_smul_mem_image_prod :
    ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (Γ : Subgroup P) (Γ₁ : Subgroup G₁) [Countable Γ₁], (∀ u ∈ Γ₁, ι u ∈ Γ) → ∀ (ν : Measure π.ker) [ν.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (D : Set π.ker) (𝓕₁ : Set G₁), (∀ x : π.ker, ∃! g : Γ.subgroupOf π.ker, g • x ∈ D) → IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → ∀ᵐ p ∂(Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)), ∃ γ : Γ, γ • p ∈ (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁)) := by sorry
