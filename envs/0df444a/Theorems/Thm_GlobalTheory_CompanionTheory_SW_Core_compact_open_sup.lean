-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_compact_open_sup
-- name    : GlobalTheory.CompanionTheory.SW.Core.compact_open_sup
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:04:16.932231+00:00
-- url     : https://prove2.me/theorems/0b0f013a-e0c6-4d1c-bb70-d39cde25c620
-- title:
--   Core: compact open sup
-- statement:
--   The Core construction uses the compact open sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CompactSubgroupAndLevel.lean#L7-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CompactSubgroupAndLevel.lean#L7-L13

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompactSubgroupAndLevel
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core

theorem GlobalTheory.CompanionTheory.SW.Core.compact_open_sup {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    {L₁ L₂ : AddSubgroup V} (h₁ : IsCompact (L₁ : Set V)) (o₁ : IsOpen (L₁ : Set V))
    (h₂ : IsCompact (L₂ : Set V)) :
    IsCompact ((L₁ ⊔ L₂ : AddSubgroup V) : Set V) ∧ IsOpen ((L₁ ⊔ L₂ : AddSubgroup V) : Set V) := by sorry
