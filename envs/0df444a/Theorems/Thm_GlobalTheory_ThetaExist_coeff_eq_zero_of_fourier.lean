-- Prove2me | Theorems.Thm_GlobalTheory_ThetaExist_coeff_eq_zero_of_fourier
-- name    : GlobalTheory.ThetaExist.coeff_eq_zero_of_fourier
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:05:06.786682+00:00
-- url     : https://prove2.me/theorems/5901d54f-6961-45ec-83d7-4f6b3004de84
-- title:
--   Theta Exist: coeff eq zero of fourier
-- statement:
--   The Theta Exist construction uses the coeff eq zero of fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/CoeffEqZeroOfOrthonormal.lean#L28-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/CoeffEqZeroOfOrthonormal.lean#L28-L51

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

theorem GlobalTheory.ThetaExist.coeff_eq_zero_of_fourier {d : Type*} [Fintype d] {c : (d → ℤ) → ℂ}
    (hc : Summable fun n => ‖c n‖)
    (h0 : ∀ t : d → ℝ, ∑' n, c n * cexp (2 * Real.pi * I * ((∑ j, (n j : ℝ) * t j : ℝ) : ℂ)) = 0)
    (k : d → ℤ) : c k = 0 := by sorry
