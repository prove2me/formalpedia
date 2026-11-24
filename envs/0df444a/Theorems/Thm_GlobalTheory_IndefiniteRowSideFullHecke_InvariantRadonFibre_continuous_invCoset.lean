-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_InvariantRadonFibre_continuous_invCoset
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.continuous_invCoset
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:14:09.131805+00:00
-- url     : https://prove2.me/theorems/5852b6ae-38ec-4173-8ef2-cec075b250a7
-- title:
--   Invariant Radon Fibre: continuous inv Coset
-- statement:
--   The Invariant Radon Fibre construction uses the continuous inv Coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/InvariantRadonFibre.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/InvariantRadonFibre.lean#L51-L53

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.continuous_invCoset : Continuous (_root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.invCoset H) := by sorry
