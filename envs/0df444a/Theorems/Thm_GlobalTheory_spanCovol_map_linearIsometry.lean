-- Prove2me | Theorems.Thm_GlobalTheory_spanCovol_map_linearIsometry
-- name    : GlobalTheory.spanCovol_map_linearIsometry
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:21:06.751269+00:00
-- url     : https://prove2.me/theorems/a1dda533-13d7-4685-992c-e98f559c17b6
-- title:
--   Global Theory: span Covol map linear Isometry
-- statement:
--   The Global Theory construction uses the span Covol map linear Isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DiscreteTopologySpanOfLinearIndependent.lean#L83-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DiscreteTopologySpanOfLinearIndependent.lean#L83-L93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DiscreteTopologySpanOfLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Module Submodule Matrix
open GlobalTheory
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.spanCovol_map_linearIsometry {L : Submodule ℤ E} (hL : L.FG) (T : E →ₗᵢ[ℝ] F) :
    spanCovol (L.map (T.toLinearMap.restrictScalars ℤ)) = spanCovol L := by sorry
