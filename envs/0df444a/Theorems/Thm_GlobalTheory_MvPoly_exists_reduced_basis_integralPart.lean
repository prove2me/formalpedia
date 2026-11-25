-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_exists_reduced_basis_integralPart
-- name    : GlobalTheory.MvPoly.exists_reduced_basis_integralPart
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:36.227959+00:00
-- url     : https://prove2.me/theorems/817ac87d-f0c9-5b08-ad91-de2c0297d58a
-- title:
--   Mv Poly: exists reduced basis integral Part
-- statement:
--   The Mv Poly construction uses the exists reduced basis integral Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsReducedBasisIntegralPartOfLinearIndependen.lean#L214-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsReducedBasisIntegralPartOfLinearIndependen.lean#L214-L245

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsShortBasisAdaptedOfSubsetSpan
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsReducedBasisIntegralPartOfLinearIndependen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule MvPolynomial NumberField
open GlobalTheory
open GlobalTheory.MvPoly
variable {K σ : Type*} [Field K]
variable [NumberField K] [Fintype σ]

theorem GlobalTheory.MvPoly.exists_reduced_basis_integralPart {κ : Type*}
    (W : Submodule K (MvPolynomial σ K)) {D : ℕ} (hD : ∀ P ∈ W, P.totalDegree ≤ D)
    (S : Set (MvPolynomial σ K)) (hSH : S ⊆ integralPart W) (hSW : span K S = W) {B : ℝ}
    (hB : ∀ P ∈ S, ∀ s : K →+* ℂ, l1Norm (map s P) ≤ B)
    (ω : κ → 𝓞 K) (hω : span ℚ (Set.range fun k => (ω k : K)) = ⊤) {A : ℝ}
    (hA : ∀ (s : K →+* ℂ) k, ‖s (ω k)‖ ≤ A) {R : ℕ} (hR : R = finrank ℚ K * finrank K W) :
    R ≤ finrank ℚ K * (1 + D) ^ Fintype.card σ ∧
    ∃ b : Basis (Fin R) ℤ (integralPart W),
      (∀ i (s : K →+* ℂ), l2Norm (map s (b i : MvPolynomial σ K)) ≤
        √((R + 3) / 4) * √(finrank ℚ K) * A * B) ∧
      (∀ i (s : K →+* ℂ), l1Norm (map s (b i : MvPolynomial σ K)) ≤
        (1 + D : ℝ) ^ ((Fintype.card σ : ℝ) / 2) * (√((R + 3) / 4) * √(finrank ℚ K) * A * B)) ∧
      (span (𝓞 K) (Set.range fun i => (b i : MvPolynomial σ K))).restrictScalars ℤ =
        integralPart W := by sorry
