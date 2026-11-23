-- Prove2me | Theorems.Thm_GlobalTheory_finrank_span_eq_finrank_int
-- name    : GlobalTheory.finrank_span_eq_finrank_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:42.328853+00:00
-- url     : https://prove2.me/theorems/4107d66f-5ca9-4412-9a57-88cace4e3a88
-- title:
--   Global Theory: finrank span eq finrank int
-- statement:
--   The Global Theory construction uses the finrank span eq finrank int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L171-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L171-L175

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

theorem GlobalTheory.finrank_span_eq_finrank_int [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] : finrank ℝ (span ℝ (L : Set E)) = finrank ℤ L := by sorry
