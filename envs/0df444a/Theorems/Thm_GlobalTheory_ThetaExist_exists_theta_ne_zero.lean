-- Prove2me | Theorems.Thm_GlobalTheory_ThetaExist_exists_theta_ne_zero
-- name    : GlobalTheory.ThetaExist.exists_theta_ne_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:11:09.847151+00:00
-- url     : https://prove2.me/theorems/7ef6d0f1-690b-4e1c-a4d9-51f98d0ac530
-- title:
--   Theta Exist: exists theta ne zero
-- statement:
--   The Theta Exist construction uses the exists theta ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/CoeffEqZeroOfOrthonormal.lean#L159-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/CoeffEqZeroOfOrthonormal.lean#L159-L183

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

theorem GlobalTheory.ThetaExist.exists_theta_ne_zero (E : Type) [Field E] [NumberField E] (X : PT E) :
    ∃ s ∈ X.Sec 1 1, s ≠ 0 := by sorry
