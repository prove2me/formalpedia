-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_exists_basis_integralPart_sum_l2Norm_sq_le
-- name    : GlobalTheory.MvPoly.exists_basis_integralPart_sum_l2Norm_sq_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:29:17.627802+00:00
-- url     : https://prove2.me/theorems/f56ff9e8-e155-494c-ac02-7981615e539b
-- title:
--   Mv Poly: exists basis integral Part sum l2 Norm sq le
-- statement:
--   The Mv Poly construction uses the exists basis integral Part sum l2 Norm sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsReducedBasisIntegralPartOfLinearIndependen.lean#L146-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsReducedBasisIntegralPartOfLinearIndependen.lean#L146-L212

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

theorem GlobalTheory.MvPoly.exists_basis_integralPart_sum_l2Norm_sq_le {κ : Type*}
    (W : Submodule K (MvPolynomial σ K)) {D : ℕ} (hD : ∀ P ∈ W, P.totalDegree ≤ D)
    (S : Set (MvPolynomial σ K)) (hSH : S ⊆ integralPart W) (hSW : span K S = W) {B : ℝ}
    (hB : ∀ P ∈ S, ∀ s : K →+* ℂ, l2Norm (map s P) ≤ B)
    (ω : κ → 𝓞 K) (hω : span ℚ (Set.range fun k => (ω k : K)) = ⊤) {A : ℝ}
    (hA : ∀ (s : K →+* ℂ) k, ‖s (ω k)‖ ≤ A) {R : ℕ} (hR : R = finrank ℚ K * finrank K W) :
    ∃ b : Basis (Fin R) ℤ (integralPart W), ∀ i,
      √(∑ s : K →+* ℂ, l2Norm (map s (b i : MvPolynomial σ K)) ^ 2) ≤
        √((R + 3) / 4) * √(finrank ℚ K) * A * B := by sorry
