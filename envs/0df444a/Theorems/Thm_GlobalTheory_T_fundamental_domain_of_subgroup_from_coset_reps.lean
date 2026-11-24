-- Prove2me | Theorems.Thm_GlobalTheory_T_fundamental_domain_of_subgroup_from_coset_reps
-- name    : GlobalTheory.T.fundamental_domain_of_subgroup_from_coset_reps
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:41:02.257812+00:00
-- url     : https://prove2.me/theorems/bad86d5f-962e-47c7-8afb-d2b170fb1a71
-- title:
--   T: fundamental domain of subgroup from coset reps
-- statement:
--   The T construction uses the fundamental domain of subgroup from coset reps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FundamentalDomainOfSubgroupFromCosetRepsStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FundamentalDomainOfSubgroupFromCosetRepsStatement.lean#L6-L7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FundamentalDomainOfSubgroupFromCosetReps
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FundamentalDomainOfSubgroupFromCosetRepsStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.fundamental_domain_of_subgroup_from_coset_reps : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Γ' : Subgroup G) [Countable Γ], Γ' ≤ Γ → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ (Q : Type) (r : Q → G), (∀ q, r q ∈ Γ) → (∀ γ ∈ Γ, ∃! q, γ * (r q)⁻¹ ∈ Γ') → ∃ 𝓕' : Set G, IsFundamentalDomain Γ' 𝓕' μ ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ h in 𝓕, ∑' q, f (r q * h) ∂μ = ∫⁻ h in 𝓕', f h ∂μ := by sorry
