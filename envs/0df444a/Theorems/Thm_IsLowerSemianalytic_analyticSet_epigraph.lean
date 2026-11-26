-- Prove2me | Theorems.Thm_IsLowerSemianalytic_analyticSet_epigraph
-- name    : IsLowerSemianalytic.analyticSet_epigraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:03:36.998859+00:00
-- url     : https://prove2.me/theorems/8264088c-d189-466a-ab66-78322a247f0f
-- title:
--   Is Lower Semianalytic: analytic Set epigraph
-- statement:
--   The epigraph condition in a real parameter is analytic.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/KernelIntegral.lean#L246-L276
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/KernelIntegral.lean#L246-L276

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

theorem IsLowerSemianalytic.analyticSet_epigraph
    {f : X × Y → ℝ≥0∞} (hf : IsLowerSemianalytic (X := X × Y) f) :
    AnalyticSet {pb : (X × Y) × ℝ | f pb.1 ≤ ENNReal.ofReal pb.2} := by sorry
