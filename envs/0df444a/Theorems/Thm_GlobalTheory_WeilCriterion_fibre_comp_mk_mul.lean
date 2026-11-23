-- Prove2me | Theorems.Thm_GlobalTheory_WeilCriterion_fibre_comp_mk_mul
-- name    : GlobalTheory.WeilCriterion.fibre_comp_mk_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:31.757028+00:00
-- url     : https://prove2.me/theorems/f95b8aea-7d25-48e1-bb85-42b9155dbde4
-- title:
--   Weil Criterion: fibre comp mk mul
-- statement:
--   The Weil Criterion construction uses the fibre comp mk mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeilCriterionInvariantMeasureHomogeneousSpace.lean#L102-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeilCriterionInvariantMeasureHomogeneousSpace.lean#L102-L106

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
omit [LocallyCompactSpace G] [T2Space G] [LocallyCompactSpace H] [SecondCountableTopology G]

theorem GlobalTheory.WeilCriterion.fibre_comp_mk_mul (ν : Measure H) {φ : G → ℝ≥0∞} (hφ : Measurable φ)
    (hφ1 : ∀ g : G, ∫⁻ h : H, φ (g * h) ∂ν = 1) (F : G ⧸ H → ℝ≥0∞) (g : G) :
    ∫⁻ h : H, F ((g * h : G) : G ⧸ H) * φ (g * h) ∂ν = F (g : G ⧸ H) := by sorry
