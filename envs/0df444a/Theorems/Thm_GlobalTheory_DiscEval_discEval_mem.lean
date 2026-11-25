-- Prove2me | Theorems.Thm_GlobalTheory_DiscEval_discEval_mem
-- name    : GlobalTheory.DiscEval.discEval_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:00:08.245327+00:00
-- url     : https://prove2.me/theorems/70c2464b-f32c-5b08-becf-d096722aa4da
-- title:
--   Disc Eval: disc Eval mem
-- statement:
--   The Disc Eval construction uses the disc Eval mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/BoundedOnFramesIffIntegralOnFrames.lean#L60-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/BoundedOnFramesIffIntegralOnFrames.lean#L60-L63

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
variable {K : Type*} [NormedField K] [CompleteSpace K] {O : Type*} [CommRing O]
  (i : O →+* K) (hi : ∀ x, ‖i x‖ ≤ 1) {t : K} (ht : ‖t‖ < 1)

theorem GlobalTheory.DiscEval.discEval_mem {B : Subring K} (hB : IsClosed (B : Set K)) (hiB : ∀ x, i x ∈ B)
    (htB : t ∈ B) (f : O⟦X⟧) : discEval i hi ht f ∈ B := by sorry
