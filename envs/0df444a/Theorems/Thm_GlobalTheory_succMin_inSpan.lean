-- Prove2me | Theorems.Thm_GlobalTheory_succMin_inSpan
-- name    : GlobalTheory.succMin_inSpan
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:40.325465+00:00
-- url     : https://prove2.me/theorems/6a57e2ba-3717-4e11-b26d-a77f41b0a0ad
-- title:
--   Global Theory: succ Min in Span
-- statement:
--   The Global Theory construction uses the succ Min in Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L258-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L258-L260

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

theorem GlobalTheory.succMin_inSpan (L : Submodule ℤ E) (i : ℕ) : succMin (inSpan L) i = succMin L i := by sorry
