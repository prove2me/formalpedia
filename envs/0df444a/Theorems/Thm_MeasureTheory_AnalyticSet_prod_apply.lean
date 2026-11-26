-- Prove2me | Theorems.Thm_MeasureTheory_AnalyticSet_prod_apply
-- name    : MeasureTheory.AnalyticSet.prod_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:03:20.846242+00:00
-- url     : https://prove2.me/theorems/ab04a712-5fdf-4f67-b4b7-b3a4d70b770a
-- title:
--   Analytic Set: prod apply
-- statement:
--   For an analytic `S` in a product of Polish spaces and finite Borel
--       measures, the product (outer) measure of `S` is the integral of the
--       (outer) measures of its sections. Uses universal measurability.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/KernelIntegral.lean#L138-L186
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/KernelIntegral.lean#L138-L186

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

theorem MeasureTheory.AnalyticSet.prod_apply
    {V W : Type*} [TopologicalSpace V] [PolishSpace V]
    [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace W] [PolishSpace W]
    [MeasurableSpace W] [BorelSpace W]
    {S : Set (V × W)} (hS : AnalyticSet S)
    (μ : Measure V) [IsFiniteMeasure μ]
    (ν : Measure W) [IsFiniteMeasure ν] :
    μ.prod ν S = ∫⁻ v, ν (Prod.mk v ⁻¹' S) ∂μ := by sorry
