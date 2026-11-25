-- Prove2me | Theorems.Thm_GlobalTheory_CanTh_thTerm_locally_normal
-- name    : GlobalTheory.CanTh.thTerm_locally_normal
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:53:38.933825+00:00
-- url     : https://prove2.me/theorems/89a61baa-9248-4a6d-863e-dc9e813f0b58
-- title:
--   Can Th: th Term locally normal
-- statement:
--   The Can Th construction uses the th Term locally normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/HasSumPolyDerivMulProdAddMatrix.lean#L162-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/HasSumPolyDerivMulProdAddMatrix.lean#L162-L176

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

theorem GlobalTheory.CanTh.thTerm_locally_normal {U : Set W} (hU : IsOpen U) {T : W → Matrix (Fin g) (Fin g) ℂ}
    {Z : W → Fin g → ℂ} (hT : ∀ i j, ContinuousOn (fun w => T w i j) U) (hZ : ContinuousOn Z U)
    (hdom : ∀ w ∈ U, T w ∈ ThetaDomain (Fin g)) (a b : Fin g → ℝ) {x : W} (hx : x ∈ U) :
    ∃ t ∈ 𝓝 x, ∃ v : (Fin g → ℤ) → ℝ, Summable v ∧
      ∀ m, ∀ w ∈ t, ‖thTerm (T w) a b (Z w) m‖ ≤ v m := by sorry
