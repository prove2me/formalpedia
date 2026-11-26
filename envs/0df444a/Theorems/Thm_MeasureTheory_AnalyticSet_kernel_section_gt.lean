-- Prove2me | Theorems.Thm_MeasureTheory_AnalyticSet_kernel_section_gt
-- name    : MeasureTheory.AnalyticSet.kernel_section_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:49.012574+00:00
-- url     : https://prove2.me/theorems/c130f55d-1842-4ec9-8e78-5036864d2801
-- title:
--   Analytic Set: kernel section gt
-- statement:
--   **Parametrized Choquet capacitability** (kernel key lemma; BS Prop 7.46):
--       for `A` analytic in `X × Y` and a finite Borel kernel `κ`, the function
--       `x ↦ κ x (A_x)` is upper semianalytic: its strict superlevel sets are
--       analytic.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L555-L597
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L555-L597

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
open ProbabilityTheory
variable {X Y : Type*}
  [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]

theorem MeasureTheory.AnalyticSet.kernel_section_gt
    {A : Set (X × Y)} (hA : AnalyticSet A)
    (κ : Kernel X Y) [IsFiniteKernel κ] (c : ℝ≥0∞) :
    AnalyticSet {x | c < κ x (Prod.mk x ⁻¹' A)} := by sorry
