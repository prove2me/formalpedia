-- Prove2me | Theorems.Thm_GlobalTheory_WeilCriterion_lintegral_mul_fibre_symm
-- name    : GlobalTheory.WeilCriterion.lintegral_mul_fibre_symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:39:50.77025+00:00
-- url     : https://prove2.me/theorems/4f5bbf12-5af3-410f-a2fc-566c57d8be23
-- title:
--   Weil Criterion: lintegral mul fibre symm
-- statement:
--   The Weil Criterion construction uses the lintegral mul fibre symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeilCriterionInvariantMeasureHomogeneousSpace.lean#L68-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeilCriterionInvariantMeasureHomogeneousSpace.lean#L68-L91

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

theorem GlobalTheory.WeilCriterion.lintegral_mul_fibre_symm
    (hΔ : ∀ h : H, modularCharacterFun (h : G) = modularCharacterFun h)
    (dg : Measure G) [dg.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]
    {f f' : G → ℝ≥0∞} (hf : Measurable f) (hf' : Measurable f') :
    ∫⁻ g, f g * ∫⁻ h : H, f' (g * h) ∂ν ∂dg = ∫⁻ g, (∫⁻ h : H, f (g * h) ∂ν) * f' g ∂dg := by sorry
