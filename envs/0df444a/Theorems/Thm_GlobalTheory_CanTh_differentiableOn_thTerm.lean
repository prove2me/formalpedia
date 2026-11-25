-- Prove2me | Theorems.Thm_GlobalTheory_CanTh_differentiableOn_thTerm
-- name    : GlobalTheory.CanTh.differentiableOn_thTerm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:54:03.392815+00:00
-- url     : https://prove2.me/theorems/032ac14e-84b7-48ba-b001-14000755b5bc
-- title:
--   Can Th: differentiable On th Term
-- statement:
--   The Can Th construction uses the differentiable On th Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/HasSumPolyDerivMulProdAddMatrix.lean#L216-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/HasSumPolyDerivMulProdAddMatrix.lean#L216-L223

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

theorem GlobalTheory.CanTh.differentiableOn_thTerm {U : Set W} {T : W → Matrix (Fin g) (Fin g) ℂ}
    {Z : W → Fin g → ℂ} (hT : ∀ i j, DifferentiableOn ℂ (fun w => T w i j) U)
    (hZ : DifferentiableOn ℂ Z U) (a b : Fin g → ℝ) (m : Fin g → ℤ) :
    DifferentiableOn ℂ (fun w => thTerm (T w) a b (Z w) m) U := by sorry
