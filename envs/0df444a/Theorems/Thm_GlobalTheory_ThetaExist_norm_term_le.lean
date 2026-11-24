-- Prove2me | Theorems.Thm_GlobalTheory_ThetaExist_norm_term_le
-- name    : GlobalTheory.ThetaExist.norm_term_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:05:44.972073+00:00
-- url     : https://prove2.me/theorems/357412fb-32b4-4a8f-b130-5d911bc71f71
-- title:
--   Theta Exist: norm term le
-- statement:
--   The Theta Exist construction uses the norm term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/CoeffEqZeroOfOrthonormal.lean#L66-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/CoeffEqZeroOfOrthonormal.lean#L66-L87

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

theorem GlobalTheory.ThetaExist.norm_term_le (Y : GT ι) (w : EuclideanSpace ℂ ι) {R : ℝ} (hw : ‖w‖ ≤ R) (γ : lat Y.b)
    {v : EuclideanSpace ℂ ι} (hv : ‖v‖ ≤ R) :
    ‖Y.ka γ * paU 1 γ (expH w) v‖ ≤ Real.exp (5 * Real.pi * R ^ 2) *
      Real.exp (-(Real.pi / 4) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2) := by sorry
