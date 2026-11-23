-- Prove2me | Theorems.Thm_GlobalTheory_WeilCriterion_measure_preimage_mul_right_eq_modulus
-- name    : GlobalTheory.WeilCriterion.measure_preimage_mul_right_eq_modulus
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:39:40.893624+00:00
-- url     : https://prove2.me/theorems/0843fc3e-f173-4dd0-887d-915cfd7aacb9
-- title:
--   Weil Criterion: measure preimage mul right eq modulus
-- statement:
--   The Weil Criterion construction uses the measure preimage mul right eq modulus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeilCriterionInvariantMeasureHomogeneousSpace.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeilCriterionInvariantMeasureHomogeneousSpace.lean#L23-L27

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

theorem GlobalTheory.WeilCriterion.measure_preimage_mul_right_eq_modulus (μ : Measure G) [μ.IsHaarMeasure] {s : Set G}
    (hs : MeasurableSet s) (g : G) :
    μ ((· * g) ⁻¹' s) = (modularCharacterFun g : ℝ≥0∞) * μ s := by sorry
