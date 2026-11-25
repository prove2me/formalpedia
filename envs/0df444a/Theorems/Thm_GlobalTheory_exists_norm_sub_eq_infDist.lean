-- Prove2me | Theorems.Thm_GlobalTheory_exists_norm_sub_eq_infDist
-- name    : GlobalTheory.exists_norm_sub_eq_infDist
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:54:41.594257+00:00
-- url     : https://prove2.me/theorems/0683367b-441c-447b-aafb-29a5dabc4e0b
-- title:
--   Global Theory: exists norm sub eq inf Dist
-- statement:
--   The Global Theory construction uses the exists norm sub eq inf Dist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L286-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L286-L291

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

theorem GlobalTheory.exists_norm_sub_eq_infDist [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] (x : E) : ∃ w ∈ L, ‖x - w‖ = Metric.infDist x (L : Set E) := by sorry
