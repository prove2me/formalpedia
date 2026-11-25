-- Prove2me | Theorems.Thm_GlobalTheory_CanTh_hasSum_polyDeriv_of_locally_normal
-- name    : GlobalTheory.CanTh.hasSum_polyDeriv_of_locally_normal
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:53:42.142983+00:00
-- url     : https://prove2.me/theorems/ef590701-20da-4a07-8366-6bf258dfdaec
-- title:
--   Can Th: has Sum poly Deriv of locally normal
-- statement:
--   The Can Th construction uses the has Sum poly Deriv of locally normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/HasSumPolyDerivMulProdAddMatrix.lean#L23-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/HasSumPolyDerivMulProdAddMatrix.lean#L23-L31

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
variable {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

theorem GlobalTheory.CanTh.hasSum_polyDeriv_of_locally_normal {ι : Type*} {F : ι → W → ℂ} {U : Set W} (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    (hle : ∀ x ∈ U, ∃ t ∈ 𝓝 x, ∃ v : ι → ℝ, Summable v ∧ ∀ i, ∀ z ∈ t, ‖F i z‖ ≤ v i)
    (P : MvPolynomial σ ℂ) (u : σ → W) {x : W} (hx : x ∈ U) :
    HasSum (fun i => I2.polyDeriv P u (F i) x) (I2.polyDeriv P u (fun w => ∑' i, F i w) x) := by sorry
