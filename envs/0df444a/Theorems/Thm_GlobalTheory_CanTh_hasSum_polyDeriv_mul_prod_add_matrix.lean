-- Prove2me | Theorems.Thm_GlobalTheory_CanTh_hasSum_polyDeriv_mul_prod_add_matrix
-- name    : GlobalTheory.CanTh.hasSum_polyDeriv_mul_prod_add_matrix
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T17:04:15.545638+00:00
-- url     : https://prove2.me/theorems/8ec5d4ca-2470-5b51-a5be-98e3096c2d6c
-- title:
--   Can Th: has Sum poly Deriv mul prod add matrix
-- statement:
--   The Can Th construction uses the has Sum poly Deriv mul prod add matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/HasSumPolyDerivMulProdAddMatrix.lean#L280-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/HasSumPolyDerivMulProdAddMatrix.lean#L280-L298

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SetIntegralPowEqZeroOfPosFreqEuclidean
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemThetaDomainIffIsSiegelAddTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsMulDotProductLeOfIsCompactThetaDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnThetaProdOfNormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasSumPolyDerivMulProdAddMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix Filter Topology ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real
open GlobalTheory GlobalTheory.CanTh
variable {g : ℕ}
variable {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
variable [FiniteDimensional ℂ W] {κ : Type*} [Fintype κ]

theorem GlobalTheory.CanTh.hasSum_polyDeriv_mul_prod_add_matrix {G : W → ℂ} {τ S : κ → Matrix (Fin g) (Fin g) ℂ}
    {Z : κ → W → Fin g → ℂ} (hG : Differentiable ℂ G) (hZ : ∀ k, Differentiable ℂ (Z k))
    (hτ : ∀ k, τ k + S k ∈ ThetaDomain (Fin g)) (a b : κ → Fin g → ℝ) (P : MvPolynomial σ ℂ)
    (u : σ → W) (x : W) :
    HasSum (fun m : κ → Fin g → ℤ =>
        I2.polyDeriv P u (fun w => G w * ∏ k, thTerm (τ k) (a k) (b k) (Z k w) (m k)) x *
          cexp (π * I * ∑ k, ((fun i => (m k i : ℂ)) + fun i => (a k i : ℂ)) ⬝ᵥ
            S k *ᵥ ((fun i => (m k i : ℂ)) + fun i => (a k i : ℂ))))
      (I2.polyDeriv P u (fun w => G w *
        ∏ k, thetaChar (τ k + S k) (fun i => (a k i : ℂ)) (fun i => (b k i : ℂ)) (Z k w)) x) := by sorry
