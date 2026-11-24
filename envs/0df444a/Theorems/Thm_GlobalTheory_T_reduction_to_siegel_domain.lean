-- Prove2me | Theorems.Thm_GlobalTheory_T_reduction_to_siegel_domain
-- name    : GlobalTheory.T.reduction_to_siegel_domain
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:10.082953+00:00
-- url     : https://prove2.me/theorems/c5d9f794-5b31-4e72-8ecd-3ca3fc958d99
-- title:
--   T: reduction to siegel domain
-- statement:
--   The T construction uses the reduction to siegel domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ReductionToSiegelDomainStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ReductionToSiegelDomainStatement.lean#L7-L8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ReductionToSiegelDomain
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ReductionToSiegelDomainStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.reduction_to_siegel_domain : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∃ (s : Finset SL(2, F)) (κ t : ℝ), 0 < κ ∧ 0 < t ∧ ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → ∃ r ∈ s, ∃ k : SL(2, F), (∀ i j, ∃ z : 𝓞 F, (z : F) = k i j) ∧ (∀ w, t ≤ (mob ρ (r * k) τ w).im) ∧ ∀ v w, κ * (mob ρ (r * k) τ w).im ≤ (mob ρ (r * k) τ v).im := by sorry
