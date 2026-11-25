-- Prove2me | Theorems.Thm_GlobalTheory_DiscEval_BoundedOnFrames_norm_coeff_linear_le
-- name    : GlobalTheory.DiscEval.BoundedOnFrames.norm_coeff_linear_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:57:05.457328+00:00
-- url     : https://prove2.me/theorems/688c66de-74fb-56f9-840c-34bff0e67bc1
-- title:
--   Bounded On Frames: norm coeff linear le
-- statement:
--   The Bounded On Frames construction uses the norm coeff linear le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/BoundedOnFramesIffIntegralOnFrames.lean#L803-L817
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/BoundedOnFramesIffIntegralOnFrames.lean#L803-L817

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

theorem GlobalTheory.DiscEval.BoundedOnFrames.norm_coeff_linear_le (hF : BoundedOnFrames i hi hπ F) {d : ℕ}
    (hd : F.IsHomogeneous d) {B : EntryIndex n n → EntryIndex n n → ℂ_[p]} {c : ℝ}
    (hc : 1 ≤ c) (hB : ∀ k l, ‖B k l‖ ≤ c) (μ : EntryIndex n n →₀ ℕ) (m : ℤ) :
    ‖(coeff μ (bind₁ (fun k => ∑ l, C (HahnSeries.C (B k l)) * X l)
        (map (laurent π A i hπ) F))).coeff m‖ ≤ c ^ d ∧
      (m < 0 → (coeff μ (bind₁ (fun k => ∑ l, C (HahnSeries.C (B k l)) * X l)
        (map (laurent π A i hπ) F))).coeff m = 0) := by sorry
