-- Prove2me | Theorems.Thm_GlobalTheory_smul_eq_map
-- name    : GlobalTheory.smul_eq_map
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:50:56.92036+00:00
-- url     : https://prove2.me/theorems/06a1f50d-4221-4dd7-9db8-86e56d0490ad
-- title:
--   Global Theory: smul eq map
-- statement:
--   The Global Theory construction uses the smul eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L266-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L266-L267

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

theorem GlobalTheory.smul_eq_map (c : ℝ) (L : Submodule ℤ E) :
    c • L = L.map ((c • LinearMap.id : E →ₗ[ℝ] E).restrictScalars ℤ) := by sorry
