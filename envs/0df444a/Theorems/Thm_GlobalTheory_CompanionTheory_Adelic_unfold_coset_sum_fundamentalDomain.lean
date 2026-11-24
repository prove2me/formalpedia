-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_unfold_coset_sum_fundamentalDomain
-- name    : GlobalTheory.CompanionTheory.Adelic.unfold_coset_sum_fundamentalDomain
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:00.435437+00:00
-- url     : https://prove2.me/theorems/9e11bd3f-2258-4069-af31-0fc9b9d10899
-- title:
--   Adelic: unfold coset sum fundamental Domain
-- statement:
--   The Adelic construction uses the unfold coset sum fundamental Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FundamentalDomainOfSubgroupFromCosetReps.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FundamentalDomainOfSubgroupFromCosetReps.lean#L9-L10

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_Nuabs
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FundamentalDomainOfSubgroupFromCosetReps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Adelic

theorem GlobalTheory.CompanionTheory.Adelic.unfold_coset_sum_fundamentalDomain : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Γ' : Subgroup G) [Countable Γ], Γ' ≤ Γ → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ (Q : Type) (r : Q → G), (∀ q, r q ∈ Γ) → (∀ γ ∈ Γ, ∃! q, γ * (r q)⁻¹ ∈ Γ') → ∃ 𝓕' : Set G, IsFundamentalDomain Γ' 𝓕' μ ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ h in 𝓕, ∑' q, f (r q * h) ∂μ = ∫⁻ h in 𝓕', f h ∂μ := by sorry
