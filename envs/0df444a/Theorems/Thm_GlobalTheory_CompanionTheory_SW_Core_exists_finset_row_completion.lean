-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_exists_finset_row_completion
-- name    : GlobalTheory.CompanionTheory.SW.Core.exists_finset_row_completion
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:04:24.795363+00:00
-- url     : https://prove2.me/theorems/194de0a8-f5c6-48be-bd0a-5329dd23dcf2
-- title:
--   Core: exists finset row completion
-- statement:
--   The Core construction uses the exists finset row completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CuspRepresentativesFinite.lean#L156-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CuspRepresentativesFinite.lean#L156-L206

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CuspRepresentativesFinite
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
open nonZeroDivisors GlobalTheory.CompanionTheory.SW.Core.RowCompletion

theorem GlobalTheory.CompanionTheory.SW.Core.exists_finset_row_completion :
    ∀ (F : Type) [Field F] [NumberField F], ∃ (s : Finset SL(2, F)) (C : ℝ), ∀ c d : 𝓞 F, (c ≠ 0 ∨ d ≠ 0) → ∃ l : F, l ≠ 0 ∧ |((Algebra.norm ℚ l : ℚ) : ℝ)| ≤ C ∧ ∀ u : (𝓞 F)ˣ, ∃ r ∈ s, ∃ k : SL(2, F), (∀ i j, ∃ z : 𝓞 F, (z : F) = k i j) ∧ (r * k) 1 0 = ((u : 𝓞 F) : F) * l * (c : F) ∧ (r * k) 1 1 = ((u : 𝓞 F) : F) * l * (d : F) := by sorry
