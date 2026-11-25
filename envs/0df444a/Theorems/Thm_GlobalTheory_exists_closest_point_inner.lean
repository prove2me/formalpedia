-- Prove2me | Theorems.Thm_GlobalTheory_exists_closest_point_inner
-- name    : GlobalTheory.exists_closest_point_inner
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:44:24.187962+00:00
-- url     : https://prove2.me/theorems/d7d55b9a-d76a-5697-a1ca-12ec35b61c02
-- title:
--   Global Theory: exists closest point inner
-- statement:
--   The Global Theory construction uses the exists closest point inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/AbsTwoMulInnerLeOfNormSubEqInfDist.lean#L196-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/AbsTwoMulInnerLeOfNormSubEqInfDist.lean#L196-L202

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

theorem GlobalTheory.exists_closest_point_inner [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] (p : E) :
    ∃ w ∈ L, (∀ z ∈ L, ‖p - w‖ ≤ ‖p - z‖) ∧ ‖p - w‖ ≤ ‖p‖ ∧
      ∀ y ∈ L, |2 * ⟪p - w, y⟫_ℝ| ≤ ‖y‖ ^ 2 := by sorry
