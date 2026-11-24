-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Span_sb_eq_sum_coset_indicators
-- name    : GlobalTheory.CompanionTheory.SW.Span.sb_eq_sum_coset_indicators
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:09:25.877306+00:00
-- url     : https://prove2.me/theorems/efb2ee91-409a-4a9e-941c-23b9b6e74ea2
-- title:
--   Span: sb eq sum coset indicators
-- statement:
--   The Span construction uses the sb eq sum coset indicators property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SbEqSumCosetIndicators.lean#L8-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SbEqSumCosetIndicators.lean#L8-L50

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SbEqSumCosetIndicators
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Span

theorem GlobalTheory.CompanionTheory.SW.Span.sb_eq_sum_coset_indicators :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ)
      (μ : Measure V), NADual V χ μ → ∀ φ : V → ℂ, SB φ → ∀ L' : AddSubgroup V,
      IsOpen (L' : Set V) → (∀ x, ∀ l ∈ L', φ (x + l) = φ x) →
      ∃ s : Finset V, ∀ x, φ x = ∑ a ∈ s, φ a * Set.indicator {y | y - a ∈ L'} (fun _ => (1 : ℂ)) x := by sorry
