-- Prove2me | Theorems.Thm_GlobalTheory_lastMin_inSpan
-- name    : GlobalTheory.lastMin_inSpan
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:54:04.619909+00:00
-- url     : https://prove2.me/theorems/c315b4e2-38ee-4e9e-bff7-a52e96cd4b00
-- title:
--   Global Theory: last Min in Span
-- statement:
--   The Global Theory construction uses the last Min in Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L262-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L262-L264

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
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem GlobalTheory.lastMin_inSpan (L : Submodule ℤ E) : lastMin (inSpan L) = lastMin L := by sorry
