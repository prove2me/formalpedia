-- Prove2me | Theorems.Thm_GlobalTheory_CanTh_hasSum_prod_thTerm
-- name    : GlobalTheory.CanTh.hasSum_prod_thTerm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:56:14.966129+00:00
-- url     : https://prove2.me/theorems/96e1da49-3a41-53bd-a85d-3cc7837bb6ef
-- title:
--   Can Th: has Sum prod th Term
-- statement:
--   The Can Th construction uses the has Sum prod th Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/HasSumPolyDerivMulProdAddMatrix.lean#L150-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/HasSumPolyDerivMulProdAddMatrix.lean#L150-L156

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

theorem GlobalTheory.CanTh.hasSum_prod_thTerm {κ : Type*} [Fintype κ] {τ : κ → Matrix (Fin g) (Fin g) ℂ}
    (hτ : ∀ k, τ k ∈ ThetaDomain (Fin g)) (a b : κ → Fin g → ℝ) (ζ : κ → Fin g → ℂ) :
    HasSum (fun m : κ → Fin g → ℤ => ∏ k, thTerm (τ k) (a k) (b k) (ζ k) (m k))
      (∏ k, thetaChar (τ k) (fun i => (a k i : ℂ)) (fun i => (b k i : ℂ)) (ζ k)) := by sorry
