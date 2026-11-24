-- Prove2me | Theorems.Thm_GlobalTheory_GlueCover_volume_finite
-- name    : GlobalTheory.GlueCover.volume_finite
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:54:47.046187+00:00
-- url     : https://prove2.me/theorems/625b4428-96ff-47c0-9230-7b1ff695b30e
-- title:
--   Glue Cover: volume finite
-- statement:
--   The Glue Cover construction uses the volume finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChartDensityChangeFormula.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChartDensityChangeFormula.lean#L18-L22

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

theorem GlobalTheory.GlueCover.volume_finite (hn : n ≠ 0) {S : Set (V n)} (hS : S.Finite) : volume S = 0 := by sorry
