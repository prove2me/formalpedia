-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_compact_for_measure_preserving_endos
-- name    : GlobalTheory.T.exists_compact_for_measure_preserving_endos
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:33:52.86395+00:00
-- url     : https://prove2.me/theorems/abaa3914-6587-47db-b2a8-64733257a185
-- title:
--   T: exists compact for measure preserving endos
-- statement:
--   The T construction uses the exists compact for measure preserving endos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsCompactForMeasurePreservingEndosStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsCompactForMeasurePreservingEndosStatement.lean#L6-L7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsCompactForMeasurePreservingEndos
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsCompactForMeasurePreservingEndosStatement
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

theorem GlobalTheory.T.exists_compact_for_measure_preserving_endos : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure], μ Set.univ = ⊤ → ∀ (Λ : Type) [AddCommGroup Λ] [Countable Λ] (j : Λ →+ V) (C : Set V), IsCompact C → (∀ y, ∃ l, y - j l ∈ C) → ∃ Ω : Set V, IsCompact Ω ∧ ∀ e : V →+ V, Continuous e → μ.map e = μ → ∃ l, l ≠ 0 ∧ e (j l) ∈ Ω := by sorry
