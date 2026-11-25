-- Prove2me | Theorems.Thm_GlobalTheory_exists_mem_norm_sub_le_lastMin
-- name    : GlobalTheory.exists_mem_norm_sub_le_lastMin
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:56:47.264121+00:00
-- url     : https://prove2.me/theorems/10f051c5-7def-457a-afca-5da26fcfc0c0
-- title:
--   Global Theory: exists mem norm sub le last Min
-- statement:
--   The Global Theory construction uses the exists mem norm sub le last Min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/AbsTwoMulInnerLeOfNormSubEqInfDist.lean#L143-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/AbsTwoMulInnerLeOfNormSubEqInfDist.lean#L143-L148

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_AbsTwoMulInnerLeOfNormSubEqInfDist
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
open scoped InnerProductSpace
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {L : Submodule ℤ E}

theorem GlobalTheory.exists_mem_norm_sub_le_lastMin [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (x : E) :
    ∃ w ∈ L, ‖x - w‖ ≤ √(finrank ℝ E) / 2 * lastMin L := by sorry
