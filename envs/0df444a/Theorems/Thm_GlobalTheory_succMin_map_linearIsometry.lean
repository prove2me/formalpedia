-- Prove2me | Theorems.Thm_GlobalTheory_succMin_map_linearIsometry
-- name    : GlobalTheory.succMin_map_linearIsometry
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:23:04.948992+00:00
-- url     : https://prove2.me/theorems/e2f726cd-c7be-4a82-9f9a-0fe27e971fa8
-- title:
--   Global Theory: succ Min map linear Isometry
-- statement:
--   The Global Theory construction uses the succ Min map linear Isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L238-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L238-L240

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

theorem GlobalTheory.succMin_map_linearIsometry (f : E →ₗᵢ[ℝ] F) (L : Submodule ℤ E) (i : ℕ) :
    succMin (L.map (f.toLinearMap.restrictScalars ℤ)) i = succMin L i := by sorry
