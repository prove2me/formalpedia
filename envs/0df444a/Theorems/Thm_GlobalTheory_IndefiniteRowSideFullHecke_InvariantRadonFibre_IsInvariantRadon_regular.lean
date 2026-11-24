-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_InvariantRadonFibre_IsInvariantRadon_regular
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.IsInvariantRadon.regular
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:54.543385+00:00
-- url     : https://prove2.me/theorems/eed9d70b-4359-4114-998f-c6ae8e99304b
-- title:
--   Is Invariant Radon: regular
-- statement:
--   The Is Invariant Radon construction uses the regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/InvariantRadonFibre.lean#L65-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/InvariantRadonFibre.lean#L65-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Topology
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)
open MeasureTheory MeasureTheory.Measure Topology
open scoped ENNReal NNReal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)
omit [MeasurableSpace G] [BorelSpace G]

theorem GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.IsInvariantRadon.regular [LocallyCompactSpace G]
    [SecondCountableTopology G] [IsClosed (H : Set G)] [MeasurableSpace (G ⧸ H)]
    [BorelSpace (G ⧸ H)] {μ : Measure (G ⧸ H)} (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.IsInvariantRadon H μ) :
    μ.Regular := by sorry
