-- Prove2me | Theorems.Thm_IsLowerSemianalytic_analyticSet_le
-- name    : IsLowerSemianalytic.analyticSet_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:03:32.691273+00:00
-- url     : https://prove2.me/theorems/0e456aa2-2d72-4a29-8e3d-b2f79766242f
-- title:
--   Is Lower Semianalytic: analytic Set le
-- statement:
--   Non-strict sublevel sets at finite levels are analytic.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/KernelIntegral.lean#L232-L242
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/KernelIntegral.lean#L232-L242

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
variable {X Y : Type*}
  [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

theorem IsLowerSemianalytic.analyticSet_le
    {f : X × Y → ℝ≥0∞} (hf : IsLowerSemianalytic (X := X × Y) f)
    {q : ℝ≥0∞} (hq : q ≠ ∞) :
    AnalyticSet {p : X × Y | f p ≤ q} := by sorry
