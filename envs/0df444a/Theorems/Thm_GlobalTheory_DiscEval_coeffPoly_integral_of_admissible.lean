-- Prove2me | Theorems.Thm_GlobalTheory_DiscEval_coeffPoly_integral_of_admissible
-- name    : GlobalTheory.DiscEval.coeffPoly_integral_of_admissible
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:58:37.739252+00:00
-- url     : https://prove2.me/theorems/9582b488-dbf2-4766-a0d2-3ec7f4f56569
-- title:
--   Disc Eval: coeff Poly integral of admissible
-- statement:
--   The Disc Eval construction uses the coeff Poly integral of admissible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/BoundedOnFramesIffIntegralOnFrames.lean#L313-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/BoundedOnFramesIffIntegralOnFrames.lean#L313-L332

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
variable {K : Type} [NormedField K] [IsUltrametricDist K]
variable [CompleteSpace K]

theorem GlobalTheory.DiscEval.coeffPoly_integral_of_admissible (K₀ : Subfield K)
    (hres : ReciprocityTheory.MultiplicativeHeights.ResidueFieldInfiniteOn (K₀ : Set K)) (S : Set K)
    (hS : ∀ t ∈ S, 0 < ‖t‖ ∧ ‖t‖ < 1)
    (hdense : ∀ r : ℝ, 0 < r → r < 1 → ∀ ε > (0 : ℝ), ∃ t ∈ S, |‖t‖ - r| < ε)
    (hrot : ∀ t ∈ S, ∀ τ ∈ K₀, ‖τ‖ = 1 → t * τ ∈ S)
    (i : O →+* K) (hi : ∀ x, ‖i x‖ ≤ 1) (hπ : i π ≠ 0) {σ : Type} [Fintype σ]
    (δ : MvPolynomial σ K) (hδ : ∀ μ, ‖coeff μ δ‖ ≤ 1) (hδ1 : ∃ μ, ‖coeff μ δ‖ = 1)
    (F : MvPolynomial σ A)
    (hF : ∀ t ∈ S, ∀ (ht0 : t ≠ 0) (ht : ‖t‖ < 1) (x : σ → K), (∀ k, x k ∈ K₀ ∧ ‖x k‖ ≤ 1) →
      ‖eval x δ‖ = 1 → ‖eval₂ (discEvalAway π A i hi hπ ht0 ht) x F‖ ≤ 1) (m : ℤ) :
    (∀ μ, ‖coeff μ (coeffPoly m (map (laurent π A i hπ) F))‖ ≤ 1) ∧
      (m < 0 → coeffPoly m (map (laurent π A i hπ) F) = 0) := by sorry
