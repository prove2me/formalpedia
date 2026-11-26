-- Prove2me | Theorems.Thm_MultiPeriod_measurable_projX
-- name    : MultiPeriod.measurable_projX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:11:22.554608+00:00
-- url     : https://prove2.me/theorems/5f1ae4e6-c255-5c54-aa8a-444e90bf5cb0
-- title:
--   Multi Period: measurable proj X
-- statement:
--   The X-side projection of a pair-history is measurable.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MultiPeriodTopology.lean#L144-L148
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MultiPeriodTopology.lean#L144-L148

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

theorem MultiPeriod.measurable_projX : ∀ t, Measurable (projX (X := X) (Y := Y) t)
  := by sorry
