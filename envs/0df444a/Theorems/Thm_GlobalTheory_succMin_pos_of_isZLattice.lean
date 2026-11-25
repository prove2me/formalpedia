-- Prove2me | Theorems.Thm_GlobalTheory_succMin_pos_of_isZLattice
-- name    : GlobalTheory.succMin_pos_of_isZLattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:47.016072+00:00
-- url     : https://prove2.me/theorems/872b98f5-b8ec-4873-bf05-b07470738cca
-- title:
--   Global Theory: succ Min pos of is ZLattice
-- statement:
--   The Global Theory construction uses the succ Min pos of is ZLattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L226-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L226-L228

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

theorem GlobalTheory.succMin_pos_of_isZLattice [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L]
    (h1 : 1 ≤ i) (hi : i ≤ finrank ℝ E) : 0 < succMin L i := by sorry
