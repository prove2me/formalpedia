-- Prove2me | Theorems.Thm_MeasureTheory_AnalyticSet_mem_analyticMeasurableSpace
-- name    : MeasureTheory.AnalyticSet.mem_analyticMeasurableSpace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:00:36.119651+00:00
-- url     : https://prove2.me/theorems/d6424a87-5f40-41dc-93a2-66666b16dcbc
-- title:
--   Analytic Set: mem analytic Measurable Space
-- statement:
--   The Analytic Set construction uses the mem analytic Measurable Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/AnalyticSigmaAlgebra.lean#L23-L26
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/AnalyticSigmaAlgebra.lean#L23-L26

import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
variable {X : Type*} [TopologicalSpace X]
open MeasureTheory MeasureTheory.AnalyticSet

theorem MeasureTheory.AnalyticSet.mem_analyticMeasurableSpace {s : Set X}
    (hs : AnalyticSet s) :
    @MeasurableSet X (analyticMeasurableSpace X) s := by sorry
