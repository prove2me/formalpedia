-- Prove2me | Theorems.Thm_GlobalTheory_CanTh_differentiableOn_polyDeriv_snd
-- name    : GlobalTheory.CanTh.differentiableOn_polyDeriv_snd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T17:05:14.817777+00:00
-- url     : https://prove2.me/theorems/9a788bad-d5d0-4e2a-a549-950c415d10a8
-- title:
--   Can Th: differentiable On poly Deriv snd
-- statement:
--   The Can Th construction uses the differentiable On poly Deriv snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/HasSumPolyDerivMulProdAddMatrix.lean#L77-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/HasSumPolyDerivMulProdAddMatrix.lean#L77-L84

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
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [FiniteDimensional ℂ B]

theorem GlobalTheory.CanTh.differentiableOn_polyDeriv_snd {F : B × W → ℂ} {U : Set (B × W)} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) (P : MvPolynomial σ ℂ) (u : σ → W) :
    DifferentiableOn ℂ (fun p : B × W => I2.polyDeriv P u (fun w => F (p.1, w)) p.2) U := by sorry
