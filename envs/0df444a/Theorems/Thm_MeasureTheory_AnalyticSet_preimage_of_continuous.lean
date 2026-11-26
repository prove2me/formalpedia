-- Prove2me | Theorems.Thm_MeasureTheory_AnalyticSet_preimage_of_continuous
-- name    : MeasureTheory.AnalyticSet.preimage_of_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:03:08.699786+00:00
-- url     : https://prove2.me/theorems/ca4535c0-0694-57cf-bcb6-9710f7213d88
-- title:
--   Analytic Set: preimage of continuous
-- statement:
--   Preimages of analytic sets under continuous maps from Polish spaces
--       are analytic (graph trick: the graph relation is closed, hence analytic,
--       and the preimage is its first-coordinate projection).
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/KernelIntegral.lean#L53-L70
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/KernelIntegral.lean#L53-L70

import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LowerSemianalytic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
set_option autoImplicit false
open Set Topology MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal
noncomputable section

theorem MeasureTheory.AnalyticSet.preimage_of_continuous
    {W V : Type*} [TopologicalSpace W] [PolishSpace W]
    [TopologicalSpace V] [T2Space V]
    {S : Set V} (hS : AnalyticSet S) {h : W → V} (hh : Continuous h) :
    AnalyticSet (h ⁻¹' S) := by sorry
