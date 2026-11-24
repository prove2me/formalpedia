-- Prove2me | Theorems.Thm_GlobalTheory_ThetaExist_differentiable_Hf
-- name    : GlobalTheory.ThetaExist.differentiable_Hf
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:05:38.206266+00:00
-- url     : https://prove2.me/theorems/39ad8237-4fdb-4250-a485-9233113a1c4c
-- title:
--   Theta Exist: differentiable Hf
-- statement:
--   The Theta Exist construction uses the differentiable Hf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/CoeffEqZeroOfOrthonormal.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/CoeffEqZeroOfOrthonormal.lean#L57-L60

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_HfNegRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
noncomputable section
open GlobalTheory GlobalTheory.ThetaExist
variable {ι : Type} [Fintype ι]

theorem GlobalTheory.ThetaExist.differentiable_Hf (a : EuclideanSpace ℂ ι) :
    Differentiable ℂ fun v : EuclideanSpace ℂ ι => Hf v a := by sorry
