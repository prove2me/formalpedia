-- Prove2me | Theorems.Thm_MeasureTheory_AnalyticSet_measure_eq_iSup_isCompact
-- name    : MeasureTheory.AnalyticSet.measure_eq_iSup_isCompact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:43.203591+00:00
-- url     : https://prove2.me/theorems/3be6196b-65f4-4be9-b99b-b0c8817af0b2
-- title:
--   Analytic Set: measure eq i Sup is Compact
-- statement:
--   **Choquet capacitability** (Kechris 30.13, measure case; BS Prop 7.42):
--       for a finite Borel measure on a Polish space, the (outer) measure of an
--       analytic set is the supremum of the measures of its compact subsets.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L369-L401
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L369-L401

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

theorem MeasureTheory.AnalyticSet.measure_eq_iSup_isCompact
    {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {A : Set X} (hA : AnalyticSet A)
    (μ : Measure X) [IsFiniteMeasure μ] :
    μ A = ⨆ (K : Set X) (_ : IsCompact K) (_ : K ⊆ A), μ K := by sorry
