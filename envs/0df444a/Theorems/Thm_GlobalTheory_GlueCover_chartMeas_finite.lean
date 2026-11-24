-- Prove2me | Theorems.Thm_GlobalTheory_GlueCover_chartMeas_finite
-- name    : GlobalTheory.GlueCover.chartMeas_finite
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:55:13.72458+00:00
-- url     : https://prove2.me/theorems/1f74cfea-642f-4cc7-9aa1-a5f41545c2d3
-- title:
--   Glue Cover: chart Meas finite
-- statement:
--   The Glue Cover construction uses the chart Meas finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChartDensityChangeFormula.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChartDensityChangeFormula.lean#L28-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ChartMeasApplyOfSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChartDensityChangeFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Topology
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal
open GlobalTheory GlobalTheory.GlueCover
open GlobalTheory.ChartGlue
variable {n : ℕ}
variable {X ι : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

theorem GlobalTheory.GlueCover.chartMeas_finite (hn : n ≠ 0) (e : OpenPartialHomeomorph X (V n)) (ρ : X → ℝ≥0∞)
    {F : Set X} (hF : F.Finite) : chartMeas e ρ F = 0 := by sorry
