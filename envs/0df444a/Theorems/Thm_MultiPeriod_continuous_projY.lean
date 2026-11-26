-- Prove2me | Theorems.Thm_MultiPeriod_continuous_projY
-- name    : MultiPeriod.continuous_projY
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:14:52.519443+00:00
-- url     : https://prove2.me/theorems/4fde8a62-7802-5ca4-88c7-e847bbc0a22d
-- title:
--   Multi Period: continuous proj Y
-- statement:
--   The Y-side projection of a pair-history is continuous.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MultiPeriodTopology.lean#L68-L72
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MultiPeriodTopology.lean#L68-L72

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

theorem MultiPeriod.continuous_projY : ∀ t, Continuous (projY (X := X) (Y := Y) t)
  := by sorry
