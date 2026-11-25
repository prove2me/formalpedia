-- Prove2me | Theorems.Thm_GlobalTheory_TupleSumPos_act_smul_vec
-- name    : GlobalTheory.TupleSumPos.act_smul_vec
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T16:20:25.126054+00:00
-- url     : https://prove2.me/theorems/be2c0ceb-f215-4a69-a27c-c9778983ddc6
-- title:
--   Tuple Sum Pos: act smul vec
-- statement:
--   The Tuple Sum Pos construction uses the act smul vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsGeneratorsLattice.lean#L89-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsGeneratorsLattice.lean#L89-L91

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_PointwiseNormSqPullbackTensorEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsNeZeroOnCoset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsGeneratorsLattice
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open scoped TensorProduct nonZeroDivisors
open GlobalTheory GlobalTheory.TupleSumPos
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.TupleSumPos.act_smul_vec {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (c : ℂ) (v : Vsp dim) :
    act α (c • v) = c • act α v := by sorry
