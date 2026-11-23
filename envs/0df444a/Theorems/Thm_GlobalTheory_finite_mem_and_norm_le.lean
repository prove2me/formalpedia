-- Prove2me | Theorems.Thm_GlobalTheory_finite_mem_and_norm_le
-- name    : GlobalTheory.finite_mem_and_norm_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:33.844804+00:00
-- url     : https://prove2.me/theorems/6609c15d-4b47-4296-ab95-6012434b1cb3
-- title:
--   Global Theory: finite mem and norm le
-- statement:
--   The Global Theory construction uses the finite mem and norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L195-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L195-L201

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

theorem GlobalTheory.finite_mem_and_norm_le [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    (R : ℝ) : {x : E | x ∈ L ∧ ‖x‖ ≤ R}.Finite := by sorry
