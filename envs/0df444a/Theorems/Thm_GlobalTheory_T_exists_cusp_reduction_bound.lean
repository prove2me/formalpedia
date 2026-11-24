-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_cusp_reduction_bound
-- name    : GlobalTheory.T.exists_cusp_reduction_bound
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:34:06.589151+00:00
-- url     : https://prove2.me/theorems/7dd5c8ed-b48f-4ce7-96a2-6953a8a97cd5
-- title:
--   T: exists cusp reduction bound
-- statement:
--   The T construction uses the exists cusp reduction bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsCuspReductionBoundStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsCuspReductionBoundStatement.lean#L7-L8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsCuspReductionBound
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsCuspReductionBoundStatement
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

theorem GlobalTheory.T.exists_cusp_reduction_bound : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∃ C : ℝ, ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → ∃ c d : 𝓞 F, (c ≠ 0 ∨ d ≠ 0) ∧ ∀ w, ‖((ρ w (c : F) : ℝ) : ℂ) * τ w + (ρ w (d : F) : ℝ)‖ ^ 2 ≤ C * (τ w).im := by sorry
