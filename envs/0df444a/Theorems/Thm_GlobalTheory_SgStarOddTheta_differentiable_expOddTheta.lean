-- Prove2me | Theorems.Thm_GlobalTheory_SgStarOddTheta_differentiable_expOddTheta
-- name    : GlobalTheory.SgStarOddTheta.differentiable_expOddTheta
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T05:32:21.902808+00:00
-- url     : https://prove2.me/theorems/e564af50-7ab5-573e-8576-087447c6dc3c
-- title:
--   Sg Star Odd Theta: differentiable exp Odd Theta
-- statement:
--   The Sg Star Odd Theta construction uses the differentiable exp Odd Theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/GaussianOddJacobiThetaEqDerivMulSgStar.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/GaussianOddJacobiThetaEqDerivMulSgStar.lean#L71-L74

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

theorem GlobalTheory.SgStarOddTheta.differentiable_expOddTheta (τ : UpperHalfPlane) : Differentiable ℂ (expOddTheta τ) := by sorry
