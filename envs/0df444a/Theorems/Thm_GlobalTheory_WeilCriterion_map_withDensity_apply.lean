-- Prove2me | Theorems.Thm_GlobalTheory_WeilCriterion_map_withDensity_apply
-- name    : GlobalTheory.WeilCriterion.map_withDensity_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:52:37.775481+00:00
-- url     : https://prove2.me/theorems/e436face-2c13-483e-97aa-38cf72e79b74
-- title:
--   Weil Criterion: map with Density apply
-- statement:
--   The Weil Criterion construction uses the map with Density apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeilCriterionInvariantMeasureHomogeneousSpace.lean#L122-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeilCriterionInvariantMeasureHomogeneousSpace.lean#L122-L130

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBruhatFunctionClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsUniqueHaarOfInvariantRadonOnCosets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeilCriterionInvariantMeasureHomogeneousSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre Topology
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.WeilCriterion
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (H : Subgroup G) [LocallyCompactSpace H]
variable [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]
omit [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [LocallyCompactSpace H]
  [IsTopologicalGroup G]

theorem GlobalTheory.WeilCriterion.map_withDensity_apply (dg : Measure G) {φ : G → ℝ≥0∞} (hφ : Measurable φ)
    {A : Set (G ⧸ H)} (hA : MeasurableSet A) :
    (dg.withDensity φ).map (QuotientGroup.mk : G → G ⧸ H) A =
      ∫⁻ g, A.indicator 1 (g : G ⧸ H) * φ g ∂dg := by sorry
