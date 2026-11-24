-- Prove2me | Theorems.Thm_GlobalTheory_ThetaExist_coeff_eq_zero_of_orthonormal
-- name    : GlobalTheory.ThetaExist.coeff_eq_zero_of_orthonormal
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:05:21.127446+00:00
-- url     : https://prove2.me/theorems/a53ba1ee-bde0-41b4-9b16-7d624a5f74ac
-- title:
--   Theta Exist: coeff eq zero of orthonormal
-- statement:
--   The Theta Exist construction uses the coeff eq zero of orthonormal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/CoeffEqZeroOfOrthonormal.lean#L13-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/CoeffEqZeroOfOrthonormal.lean#L13-L26

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

theorem GlobalTheory.ThetaExist.coeff_eq_zero_of_orthonormal {C H κ : Type*} [NormedAddCommGroup C] [NormedSpace ℂ C]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : C →L[ℂ] H) (e : κ → C)
    (h : Orthonormal ℂ fun i => T (e i)) {c : κ → ℂ} (hs : HasSum (fun i => c i • e i) 0)
    (k : κ) : c k = 0 := by sorry
