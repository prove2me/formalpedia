-- Prove2me | Theorems.Thm_GlobalTheory_natCast_le_rank_of_le_finrank
-- name    : GlobalTheory.natCast_le_rank_of_le_finrank
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:32.018853+00:00
-- url     : https://prove2.me/theorems/919efc91-26b2-4dab-ab6c-ace633677b97
-- title:
--   Global Theory: nat Cast le rank of le finrank
-- statement:
--   The Global Theory construction uses the nat Cast le rank of le finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L185-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L185-L187

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

theorem GlobalTheory.natCast_le_rank_of_le_finrank {K W : Type*} [DivisionRing K] [AddCommGroup W] [Module K W]
    (h : i ≤ finrank K W) : (i : Cardinal) ≤ Module.rank K W := by sorry
