-- Prove2me | Theorems.Thm_GlobalTheory_T_parabolic_fundamental_domain_split
-- name    : GlobalTheory.T.parabolic_fundamental_domain_split
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:55:08.900078+00:00
-- url     : https://prove2.me/theorems/1b0127cc-7b7e-4950-b08c-6a9a6fc65392
-- title:
--   T: parabolic fundamental domain split
-- statement:
--   The T construction uses the parabolic fundamental domain split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ParabolicFundamentalDomainSplitStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ParabolicFundamentalDomainSplitStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicFundamentalDomainSplit
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SplitHomeoApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteCovolumeUnimodular
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicFundamentalDomainSplitStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.parabolic_fundamental_domain_split : ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (Γ : Subgroup P) [Countable Γ], (∃ U ∈ 𝓝 (1 : P), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → (∃ K : Set P, IsCompact K ∧ ∀ m ∈ π.ker, ∃ γ ∈ Γ, π γ = 1 ∧ γ * m ∈ K) → ∃ D : Set π.ker, MeasurableSet D ∧ (∀ x : π.ker, ∃! g : Γ.subgroupOf π.ker, g • x ∈ D) ∧ ∀ (ν : Measure π.ker) [ν.IsHaarMeasure], IsFundamentalDomain (Γ.subgroupOf π.ker) D ν ∧ ν D ≠ 0 ∧ ν D < ⊤ := by sorry
