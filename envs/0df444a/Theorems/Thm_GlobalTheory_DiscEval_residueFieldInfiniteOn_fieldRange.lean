-- Prove2me | Theorems.Thm_GlobalTheory_DiscEval_residueFieldInfiniteOn_fieldRange
-- name    : GlobalTheory.DiscEval.residueFieldInfiniteOn_fieldRange
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:57:47.051804+00:00
-- url     : https://prove2.me/theorems/862a3f6c-d4ae-5458-8faf-ef648fb6f5a3
-- title:
--   Disc Eval: residue Field Infinite On field Range
-- statement:
--   The Disc Eval construction uses the residue Field Infinite On field Range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/BoundedOnFramesIffIntegralOnFrames.lean#L346-L366
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/BoundedOnFramesIffIntegralOnFrames.lean#L346-L366

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

theorem GlobalTheory.DiscEval.residueFieldInfiniteOn_fieldRange {C K : Type*} [NormedField C] [IsUltrametricDist C]
    [IsAlgClosed C] [NormedField K] [IsUltrametricDist K] (e : C →+* K) (he : ∀ x, ‖e x‖ = ‖x‖) :
    ReciprocityTheory.MultiplicativeHeights.ResidueFieldInfiniteOn (e.fieldRange : Set K) := by sorry
