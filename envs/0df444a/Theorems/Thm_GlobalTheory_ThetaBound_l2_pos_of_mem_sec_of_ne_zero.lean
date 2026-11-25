-- Prove2me | Theorems.Thm_GlobalTheory_ThetaBound_l2_pos_of_mem_sec_of_ne_zero
-- name    : GlobalTheory.ThetaBound.l2_pos_of_mem_sec_of_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:41:48.503879+00:00
-- url     : https://prove2.me/theorems/197cb925-3c37-5d48-aa20-621445ab4fb4
-- title:
--   Theta Bound: l2 pos of mem sec of ne zero
-- statement:
--   The Theta Bound construction uses the l2 pos of mem sec of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/PointwiseNormSqPullbackTensorEqProd.lean#L139-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/PointwiseNormSqPullbackTensorEqProd.lean#L139-L143

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_SupLeL2PrincipalTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardToMultisetEqDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_PointwiseNormSqPullbackTensorEqProd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim

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
open TensorLat
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.ThetaBound.l2_pos_of_mem_sec_of_ne_zero (X : PT E) {q : ℕ} (hq : 1 ≤ q) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec q 1)
    (hne : s ≠ 0) : 0 < X.l2 q s := by sorry
