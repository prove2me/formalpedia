-- Prove2me | Theorems.Thm_MultiPeriod_continuous_projX
-- name    : MultiPeriod.continuous_projX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:14:58.886975+00:00
-- url     : https://prove2.me/theorems/e337f5a7-ec2d-4d5d-b8ee-4c1b11788cc8
-- title:
--   Multi Period: continuous proj X
-- statement:
--   The X-side projection of a pair-history is continuous.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MultiPeriodTopology.lean#L61-L65
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MultiPeriodTopology.lean#L61-L65

import Definitions.Def_BicausalOT_MultiPeriod
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Definitions.Def_BicausalOT_MultiPeriodTopology
set_option autoImplicit false
open MeasureTheory
noncomputable section
open MultiPeriod
variable (X Y : ℕ → Type*)
variable [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]
variable {X Y}

theorem MultiPeriod.continuous_projX : ∀ t, Continuous (projX (X := X) (Y := Y) t)
  := by sorry
