-- Prove2me | Theorems.Thm_MeasureTheory_AnalyticSet_nullMeasurableSet
-- name    : MeasureTheory.AnalyticSet.nullMeasurableSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:41.263419+00:00
-- url     : https://prove2.me/theorems/5514ad6d-6435-5b91-b8d6-71cbfa4ab454
-- title:
--   Analytic Set: null Measurable Set
-- statement:
--   **Analytic sets are universally measurable** (Lusin; BS Prop 7.42):
--       null-measurable with respect to every finite Borel measure.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L405-L452
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L405-L452

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Tactic.Finiteness
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
set_option autoImplicit false
open Set Topology MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section
variable {Z : Type*} [TopologicalSpace Z]

theorem MeasureTheory.AnalyticSet.nullMeasurableSet
    {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {A : Set X} (hA : AnalyticSet A)
    (μ : Measure X) [IsFiniteMeasure μ] :
    NullMeasurableSet A μ := by sorry
