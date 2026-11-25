-- Prove2me | Theorems.Thm_GlobalTheory_ThetaBound_le_firstMinimum_of_period_lower_bound
-- name    : GlobalTheory.ThetaBound.le_firstMinimum_of_period_lower_bound
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:41:32.792735+00:00
-- url     : https://prove2.me/theorems/6672d219-27da-5497-9097-d12db63d2175
-- title:
--   Theta Bound: le first Minimum of period lower bound
-- statement:
--   The Theta Bound construction uses the le first Minimum of period lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/PointwiseNormSqPullbackTensorEqProd.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/PointwiseNormSqPullbackTensorEqProd.lean#L27-L32

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

theorem GlobalTheory.ThetaBound.le_firstMinimum_of_period_lower_bound (Y : GT ι) (hι : Fintype.card ι ≠ 0) {lam : ℝ}
    (hmin : ∀ x ∈ lat Y.b, x ≠ 0 → lam ≤ ‖x‖) : lam ≤ Y.la1 := by sorry
