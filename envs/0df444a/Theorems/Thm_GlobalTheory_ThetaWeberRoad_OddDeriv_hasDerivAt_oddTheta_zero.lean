-- Prove2me | Theorems.Thm_GlobalTheory_ThetaWeberRoad_OddDeriv_hasDerivAt_oddTheta_zero
-- name    : GlobalTheory.ThetaWeberRoad.OddDeriv.hasDerivAt_oddTheta_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T05:32:09.168559+00:00
-- url     : https://prove2.me/theorems/773e76e3-948e-4b68-9968-95ac0a0e2f4d
-- title:
--   Odd Deriv: has Deriv At odd Theta zero
-- statement:
--   The Odd Deriv construction uses the has Deriv At odd Theta zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/HasDerivAtOddJacobiThetaZeroEtaCube.lean#L106-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/HasDerivAtOddJacobiThetaZeroEtaCube.lean#L106-L153

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HasDerivAtOddJacobiThetaZeroEtaCube
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open UpperHalfPlane hiding I
open scoped Real
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.ThetaWeberRoad GlobalTheory.ThetaWeberRoad.OddDeriv

theorem GlobalTheory.ThetaWeberRoad.OddDeriv.hasDerivAt_oddTheta_zero :
    TripleProduct → ∀ τ : UpperHalfPlane,
      HasDerivAt (oddTheta τ) (-2 * (Real.pi : ℂ) * ModularForm.eta (τ : ℂ) ^ 3) 0 := by sorry
