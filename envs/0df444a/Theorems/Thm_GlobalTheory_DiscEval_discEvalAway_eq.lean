-- Prove2me | Theorems.Thm_GlobalTheory_DiscEval_discEvalAway_eq
-- name    : GlobalTheory.DiscEval.discEvalAway_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:58:37.619126+00:00
-- url     : https://prove2.me/theorems/0e1dcd5e-6c8a-4ca9-bb6a-96af7bb39966
-- title:
--   Disc Eval: disc Eval Away eq
-- statement:
--   The Disc Eval construction uses the disc Eval Away eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/BoundedOnFramesIffIntegralOnFrames.lean#L135-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/BoundedOnFramesIffIntegralOnFrames.lean#L135-L141

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
variable {K : Type*} {O : Type*} [CommRing O] (π : O)
  (A : Type*) [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]
variable [NormedField K] [CompleteSpace K] (i : O →+* K) (hi : ∀ x, ‖i x‖ ≤ 1) (hπ : i π ≠ 0)
  {t : K} (ht0 : t ≠ 0) (ht : ‖t‖ < 1)
variable {π A}

theorem GlobalTheory.DiscEval.discEvalAway_eq {f : A} {a b : ℕ} {f₀ : O⟦X⟧}
    (h : f * algebraMap O⟦X⟧ A (PowerSeries.C π ^ a * PowerSeries.X ^ b) = algebraMap O⟦X⟧ A f₀) :
    discEvalAway π A i hi hπ ht0 ht f = (i π)⁻¹ ^ a * t⁻¹ ^ b * discEval i hi ht f₀ := by sorry
