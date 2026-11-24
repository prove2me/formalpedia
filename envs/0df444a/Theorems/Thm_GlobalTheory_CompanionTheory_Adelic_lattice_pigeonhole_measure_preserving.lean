-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_lattice_pigeonhole_measure_preserving
-- name    : GlobalTheory.CompanionTheory.Adelic.lattice_pigeonhole_measure_preserving
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:15:56.136814+00:00
-- url     : https://prove2.me/theorems/88ec3290-2049-43ca-8ca5-bb116339c035
-- title:
--   Adelic: lattice pigeonhole measure preserving
-- statement:
--   The Adelic construction uses the lattice pigeonhole measure preserving property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsCompactForMeasurePreservingEndos.lean#L8-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsCompactForMeasurePreservingEndos.lean#L8-L67

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsCompactForMeasurePreservingEndos
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

theorem GlobalTheory.CompanionTheory.Adelic.lattice_pigeonhole_measure_preserving :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
      [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
      (μ : Measure V) [μ.IsAddHaarMeasure], μ Set.univ = ⊤ →
      ∀ (Λ : Type) [AddCommGroup Λ] [Countable Λ] (j : Λ →+ V) (C : Set V), IsCompact C →
        (∀ y, ∃ l, y - j l ∈ C) →
        ∃ Ω : Set V, IsCompact Ω ∧ ∀ e : V →+ V, Continuous e → μ.map e = μ →
          ∃ l, l ≠ 0 ∧ e (j l) ∈ Ω := by sorry
