-- Prove2me | Theorems.Thm_GlobalTheory_coveringRadius_inSpan_le_lastMin
-- name    : GlobalTheory.coveringRadius_inSpan_le_lastMin
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:44:48.971024+00:00
-- url     : https://prove2.me/theorems/de7a3644-ce62-5d49-b17f-b304e640ae33
-- title:
--   Global Theory: covering Radius in Span le last Min
-- statement:
--   The Global Theory construction uses the covering Radius in Span le last Min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/AbsTwoMulInnerLeOfNormSubEqInfDist.lean#L155-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/AbsTwoMulInnerLeOfNormSubEqInfDist.lean#L155-L158

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

theorem GlobalTheory.coveringRadius_inSpan_le_lastMin [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] : coveringRadius (inSpan L) ≤ √(finrank ℤ L) / 2 * lastMin L := by sorry
