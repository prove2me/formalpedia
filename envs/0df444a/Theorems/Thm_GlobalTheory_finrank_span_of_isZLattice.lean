-- Prove2me | Theorems.Thm_GlobalTheory_finrank_span_of_isZLattice
-- name    : GlobalTheory.finrank_span_of_isZLattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:37.818188+00:00
-- url     : https://prove2.me/theorems/ab6dd8a2-551a-44b9-a4c7-26787cb51139
-- title:
--   Global Theory: finrank span of is ZLattice
-- statement:
--   The Global Theory construction uses the finrank span of is ZLattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L177-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L177-L179

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

theorem GlobalTheory.finrank_span_of_isZLattice (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    finrank ℝ (span ℝ (L : Set E)) = finrank ℝ E := by sorry
