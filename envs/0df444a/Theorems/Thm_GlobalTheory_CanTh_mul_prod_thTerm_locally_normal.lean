-- Prove2me | Theorems.Thm_GlobalTheory_CanTh_mul_prod_thTerm_locally_normal
-- name    : GlobalTheory.CanTh.mul_prod_thTerm_locally_normal
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:57:14.034205+00:00
-- url     : https://prove2.me/theorems/6f76f13b-2569-57b1-9d15-6b737c788132
-- title:
--   Can Th: mul prod th Term locally normal
-- statement:
--   The Can Th construction uses the mul prod th Term locally normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/HasSumPolyDerivMulProdAddMatrix.lean#L178-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/HasSumPolyDerivMulProdAddMatrix.lean#L178-L197

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
variable {W : Type*} [TopologicalSpace W] [LocallyCompactSpace W]

theorem GlobalTheory.CanTh.mul_prod_thTerm_locally_normal {κ : Type*} [Fintype κ] {U : Set W} (hU : IsOpen U)
    {G : W → ℂ} {T : κ → W → Matrix (Fin g) (Fin g) ℂ} {Z : κ → W → Fin g → ℂ}
    (hG : ContinuousOn G U) (hT : ∀ k i j, ContinuousOn (fun w => T k w i j) U)
    (hZ : ∀ k, ContinuousOn (Z k) U) (hdom : ∀ k, ∀ w ∈ U, T k w ∈ ThetaDomain (Fin g))
    (a b : κ → Fin g → ℝ) {x : W} (hx : x ∈ U) :
    ∃ t ∈ 𝓝 x, ∃ v : (κ → Fin g → ℤ) → ℝ, Summable v ∧
      ∀ m, ∀ w ∈ t, ‖G w * ∏ k, thTerm (T k w) (a k) (b k) (Z k w) (m k)‖ ≤ v m := by sorry
