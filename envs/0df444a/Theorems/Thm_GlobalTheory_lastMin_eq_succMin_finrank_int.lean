-- Prove2me | Theorems.Thm_GlobalTheory_lastMin_eq_succMin_finrank_int
-- name    : GlobalTheory.lastMin_eq_succMin_finrank_int
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:48:24.619835+00:00
-- url     : https://prove2.me/theorems/21700cd3-eb4c-4537-8029-69a6db323619
-- title:
--   Global Theory: last Min eq succ Min finrank int
-- statement:
--   The Global Theory construction uses the last Min eq succ Min finrank int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L181-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L181-L183

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open scoped Pointwise
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {L L' : Submodule ℤ E} {i j : ℕ} {r : ℝ}

theorem GlobalTheory.lastMin_eq_succMin_finrank_int [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] : lastMin L = succMin L (finrank ℤ L) := by sorry
