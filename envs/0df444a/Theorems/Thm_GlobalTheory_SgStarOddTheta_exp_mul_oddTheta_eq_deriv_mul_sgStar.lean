-- Prove2me | Theorems.Thm_GlobalTheory_SgStarOddTheta_exp_mul_oddTheta_eq_deriv_mul_sgStar
-- name    : GlobalTheory.SgStarOddTheta.exp_mul_oddTheta_eq_deriv_mul_sgStar
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T05:32:25.180141+00:00
-- url     : https://prove2.me/theorems/b33cdbb8-1951-59c5-afd3-875ddc5bc083
-- title:
--   Sg Star Odd Theta: exp mul odd Theta eq deriv mul sg Star
-- statement:
--   The Sg Star Odd Theta construction uses the exp mul odd Theta eq deriv mul sg Star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/GaussianOddJacobiThetaEqDerivMulSgStar.lean#L100-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/GaussianOddJacobiThetaEqDerivMulSgStar.lean#L100-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_GaussianOddJacobiThetaEqDerivMulSgStar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open GlobalTheory GlobalTheory.SgStarOddTheta
open Formalism.L2.Th1.F

theorem GlobalTheory.SgStarOddTheta.exp_mul_oddTheta_eq_deriv_mul_sgStar :
    Formalism.L2.Th1.F.ThetaLine → Formalism.L2.Th1.F.SgStarBasic → ∀ (τ : UpperHalfPlane) (z : ℂ),
      Complex.exp ((Real.pi : ℂ) * z ^ 2 / (2 * ((τ.im : ℝ) : ℂ))) * GlobalTheory.ThetaWeberRoad.oddTheta τ z =
        deriv (GlobalTheory.ThetaWeberRoad.oddTheta τ) 0 * Formalism.L2.Th1.F.sgStar (GlobalTheory.periodPairOfTau τ) z := by sorry
