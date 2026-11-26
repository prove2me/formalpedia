-- Prove2me | Theorems.Thm_MultiPeriod_measurable_projY
-- name    : MultiPeriod.measurable_projY
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:11:33.704395+00:00
-- url     : https://prove2.me/theorems/a48b04c6-a0c7-5516-86f1-cc0497e3b078
-- title:
--   Multi Period: measurable proj Y
-- statement:
--   The Y-side projection of a pair-history is measurable.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MultiPeriodTopology.lean#L151-L155
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MultiPeriodTopology.lean#L151-L155

import Definitions.Def_BicausalOT_MultiPeriod
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Definitions.Def_BicausalOT_MultiPeriodTopology
set_option autoImplicit false
open MeasureTheory
noncomputable section
open MultiPeriod
variable (X Y : ℕ → Type*)
variable [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
variable {X Y}

theorem MultiPeriod.measurable_projY : ∀ t, Measurable (projY (X := X) (Y := Y) t)
  := by sorry
