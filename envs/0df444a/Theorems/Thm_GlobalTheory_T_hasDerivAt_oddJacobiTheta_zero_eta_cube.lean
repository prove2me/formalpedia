-- Prove2me | Theorems.Thm_GlobalTheory_T_hasDerivAt_oddJacobiTheta_zero_eta_cube
-- name    : GlobalTheory.T.hasDerivAt_oddJacobiTheta_zero_eta_cube
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-27T05:36:37.665638+00:00
-- url     : https://prove2.me/theorems/7dd26f59-3f2e-522e-9062-f386981e4c21
-- title:
--   T: has Deriv At odd Jacobi Theta zero eta cube
-- statement:
--   The T construction uses the has Deriv At odd Jacobi Theta zero eta cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/HasDerivAtOddJacobiThetaZeroEtaCubeStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/HasDerivAtOddJacobiThetaZeroEtaCubeStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HasDerivAtOddJacobiThetaZeroEtaCube
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HasDerivAtOddJacobiThetaZeroEtaCubeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hasDerivAt_oddJacobiTheta_zero_eta_cube : GlobalTheory.ThetaWeberRoad.TripleProduct → ∀ τ : UpperHalfPlane, HasDerivAt (GlobalTheory.ThetaWeberRoad.oddTheta τ) (-2 * (Real.pi : ℂ) * ModularForm.eta (τ : ℂ) ^ 3) 0 := by sorry
