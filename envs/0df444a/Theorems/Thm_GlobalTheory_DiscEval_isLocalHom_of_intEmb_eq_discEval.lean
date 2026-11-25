-- Prove2me | Theorems.Thm_GlobalTheory_DiscEval_isLocalHom_of_intEmb_eq_discEval
-- name    : GlobalTheory.DiscEval.isLocalHom_of_intEmb_eq_discEval
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:58:01.266797+00:00
-- url     : https://prove2.me/theorems/261bd91d-4bb1-478c-a250-0a5b297c5be1
-- title:
--   Disc Eval: is Local Hom of int Emb eq disc Eval
-- statement:
--   The Disc Eval construction uses the is Local Hom of int Emb eq disc Eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/BoundedOnFramesIffIntegralOnFrames.lean#L634-L645
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/BoundedOnFramesIffIntegralOnFrames.lean#L634-L645

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
variable (p : ℕ) [Fact p.Prime]
variable {p}
variable {O : Type*} [CommRing O] [Algebra ℤ_[p] O] (i : O →+* ℂ_[p]) (hi : ∀ x, ‖i x‖ ≤ 1)
variable [Module.Finite ℤ_[p] O]
include hi
variable (L : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] L]
omit [Module.Finite ℤ_[p] O]

theorem GlobalTheory.DiscEval.isLocalHom_of_intEmb_eq_discEval (hinj : Function.Injective i) {t : ℂ_[p]} (ht : ‖t‖ < 1)
    {ev : O⟦X⟧ →+* integralClosure ℤ_[p] L} (hev : ∀ f, intEmb L (ev f) = discEval i hi ht f) :
    IsLocalHom ev := by sorry
