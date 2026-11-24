-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_compact_part_closed_orbit
-- name    : GlobalTheory.CompanionTheory.Adelic.compact_part_closed_orbit
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:16:41.329572+00:00
-- url     : https://prove2.me/theorems/b4260d70-58e6-4725-a82a-ebf3cfdbd46c
-- title:
--   Adelic: compact part closed orbit
-- statement:
--   The Adelic construction uses the compact part closed orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CompactPartClosedOrbit.lean#L8-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CompactPartClosedOrbit.lean#L8-L54

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompactPartClosedOrbit
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

theorem GlobalTheory.CompanionTheory.Adelic.compact_part_closed_orbit :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
      [LocallyCompactSpace G] [SecondCountableTopology G] (V : Type) [TopologicalSpace V]
      [T2Space V] [LocallyCompactSpace V] (a : G → V → V),
      (Continuous fun p : G × V => a p.1 p.2) → (∀ y, a 1 y = y) →
      (∀ g h y, a (g * h) y = a g (a h y)) →
      ∀ (Z : Set V) (x : V), IsClosed Z → (∀ y, y ∈ Z ↔ ∃ g, a g x = y) →
      ∀ Ω : Set V, IsCompact Ω → ∃ C : Set G, IsCompact C ∧ ∀ y ∈ Ω, y ∈ Z → ∃ c ∈ C, a c x = y := by sorry
