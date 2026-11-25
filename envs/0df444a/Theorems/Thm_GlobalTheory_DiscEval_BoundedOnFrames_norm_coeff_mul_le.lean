-- Prove2me | Theorems.Thm_GlobalTheory_DiscEval_BoundedOnFrames_norm_coeff_mul_le
-- name    : GlobalTheory.DiscEval.BoundedOnFrames.norm_coeff_mul_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:05:16.109596+00:00
-- url     : https://prove2.me/theorems/aecf66e9-c7b1-4650-8fdf-3c911fc42164
-- title:
--   Bounded On Frames: norm coeff mul le
-- statement:
--   The Bounded On Frames construction uses the norm coeff mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/BoundedOnFramesIffIntegralOnFrames.lean#L819-L838
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/BoundedOnFramesIffIntegralOnFrames.lean#L819-L838

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
open MvPolynomial
variable {O : Type*} [CommRing O] (i : O →+* ℂ_[p]) (hi : ∀ x, ‖i x‖ ≤ 1) {π : O} (hπ : i π ≠ 0)
  {A : Type*} [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]
  {ι : Type} [Fintype ι] {n : ι → Type} [∀ s, Fintype (n s)] [∀ s, DecidableEq (n s)]
variable {i hi hπ} {F : MvPolynomial (EntryIndex n n) A}

theorem GlobalTheory.DiscEval.BoundedOnFrames.norm_coeff_mul_le (hF : BoundedOnFrames i hi hπ F) {d : ℕ}
    (hd : F.IsHomogeneous d) {κ : ι → Type*} [∀ s, Fintype (κ s)]
    {w : ∀ s, Matrix (n s) (κ s) ℂ_[p]} {c : ℝ} (hc : 0 ≤ c) (hw : ∀ s a b, ‖w s a b‖ ≤ c)
    (μ : EntryIndex κ n →₀ ℕ) (m : ℤ) :
    ‖(coeff μ (bind₁ (fun k => ∑ j, C (HahnSeries.C (w k.1 k.2.1 j)) * X ⟨k.1, j, k.2.2⟩)
        (map (laurent π A i hπ) F))).coeff m‖ ≤ c ^ d ∧
      (m < 0 → (coeff μ (bind₁ (fun k => ∑ j, C (HahnSeries.C (w k.1 k.2.1 j)) * X ⟨k.1, j, k.2.2⟩)
        (map (laurent π A i hπ) F))).coeff m = 0) := by sorry
