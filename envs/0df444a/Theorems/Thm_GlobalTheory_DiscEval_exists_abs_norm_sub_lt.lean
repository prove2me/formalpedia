-- Prove2me | Theorems.Thm_GlobalTheory_DiscEval_exists_abs_norm_sub_lt
-- name    : GlobalTheory.DiscEval.exists_abs_norm_sub_lt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:58:36.055323+00:00
-- url     : https://prove2.me/theorems/897ede5a-9223-4973-99aa-a7694c082987
-- title:
--   Disc Eval: exists abs norm sub lt
-- statement:
--   The Disc Eval construction uses the exists abs norm sub lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/BoundedOnFramesIffIntegralOnFrames.lean#L368-L378
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/BoundedOnFramesIffIntegralOnFrames.lean#L368-L378

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DiscEval
open Filter Topology IsLocalRing
open scoped PowerSeries LaurentSeries

theorem GlobalTheory.DiscEval.exists_abs_norm_sub_lt {C : Type*} [NontriviallyNormedField C] [IsAlgClosed C] {r ε : ℝ}
    (h0 : 0 < r) (h1 : r < 1) (hε : 0 < ε) : ∃ x : C, 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ |‖x‖ - r| < ε := by sorry
