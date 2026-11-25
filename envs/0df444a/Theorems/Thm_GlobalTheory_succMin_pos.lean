-- Prove2me | Theorems.Thm_GlobalTheory_succMin_pos
-- name    : GlobalTheory.succMin_pos
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:22:34.7408+00:00
-- url     : https://prove2.me/theorems/d60ecd28-70e4-4fd1-8d9a-1c3949d9d607
-- title:
--   Global Theory: succ Min pos
-- statement:
--   The Global Theory construction uses the succ Min pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L221-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L221-L224

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

theorem GlobalTheory.succMin_pos [FiniteDimensional ℝ E] [DiscreteTopology L] (h1 : 1 ≤ i)
    (hi : i ≤ finrank ℝ (span ℝ (L : Set E))) : 0 < succMin L i := by sorry
