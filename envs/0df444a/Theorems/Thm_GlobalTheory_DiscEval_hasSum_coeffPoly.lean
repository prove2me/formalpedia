-- Prove2me | Theorems.Thm_GlobalTheory_DiscEval_hasSum_coeffPoly
-- name    : GlobalTheory.DiscEval.hasSum_coeffPoly
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:57:55.59887+00:00
-- url     : https://prove2.me/theorems/46c672e7-a702-5cc1-b039-12d9bd993155
-- title:
--   Disc Eval: has Sum coeff Poly
-- statement:
--   The Disc Eval construction uses the has Sum coeff Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/BoundedOnFramesIffIntegralOnFrames.lean#L237-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/BoundedOnFramesIffIntegralOnFrames.lean#L237-L257

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
open MvPolynomial
variable {O : Type*} [CommRing O] {π : O}
  {A : Type*} [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]

theorem GlobalTheory.DiscEval.hasSum_coeffPoly {K : Type*} [NormedField K] [CompleteSpace K] (i : O →+* K)
    (hi : ∀ x, ‖i x‖ ≤ 1) (hπ : i π ≠ 0) {t : K} (ht0 : t ≠ 0) (ht : ‖t‖ < 1) {σ : Type*}
    (F : MvPolynomial σ A) (x : σ → K) :
    HasSum (fun m : ℤ => eval x (coeffPoly m (map (laurent π A i hπ) F)) * t ^ m)
      (eval₂ (discEvalAway π A i hi hπ ht0 ht) x F) := by sorry
