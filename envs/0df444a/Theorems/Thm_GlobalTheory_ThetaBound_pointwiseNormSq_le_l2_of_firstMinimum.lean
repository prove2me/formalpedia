-- Prove2me | Theorems.Thm_GlobalTheory_ThetaBound_pointwiseNormSq_le_l2_of_firstMinimum
-- name    : GlobalTheory.ThetaBound.pointwiseNormSq_le_l2_of_firstMinimum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:42:35.967652+00:00
-- url     : https://prove2.me/theorems/1b2fecbc-d908-4e67-8091-b1eab7aa5772
-- title:
--   Theta Bound: pointwise Norm Sq le l2 of first Minimum
-- statement:
--   The Theta Bound construction uses the pointwise Norm Sq le l2 of first Minimum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/PointwiseNormSqPullbackTensorEqProd.lean#L34-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/PointwiseNormSqPullbackTensorEqProd.lean#L34-L48

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_SupLeL2PrincipalTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardToMultisetEqDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_PointwiseNormSqPullbackTensorEqProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open GlobalTheory.ThetaBound
variable {ι : Type} [Fintype ι]

theorem GlobalTheory.ThetaBound.pointwiseNormSq_le_l2_of_firstMinimum (hsup : GSupStatement) (Y : GT ι) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ Y.Sec 1)
    {lam : ℝ} (hlam : 0 < lam) (hmin : ∀ x ∈ lat Y.b, x ≠ 0 → lam ≤ ‖x‖)
    (v : EuclideanSpace ℂ ι) :
    Y.ptN2 1 F v ≤ (Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * Fintype.card ι) /
      (Real.sqrt Real.pi * lam)) ^ Fintype.card ι) ^ 2 * Y.l2 1 F := by sorry
