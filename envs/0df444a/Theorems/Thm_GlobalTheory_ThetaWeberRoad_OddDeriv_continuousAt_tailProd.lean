-- Prove2me | Theorems.Thm_GlobalTheory_ThetaWeberRoad_OddDeriv_continuousAt_tailProd
-- name    : GlobalTheory.ThetaWeberRoad.OddDeriv.continuousAt_tailProd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T05:33:32.825107+00:00
-- url     : https://prove2.me/theorems/0d02d5f7-a4c2-4786-ab2f-674e33fd56fe
-- title:
--   Odd Deriv: continuous At tail Prod
-- statement:
--   The Odd Deriv construction uses the continuous At tail Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/HasDerivAtOddJacobiThetaZeroEtaCube.lean#L28-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/HasDerivAtOddJacobiThetaZeroEtaCube.lean#L28-L46

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

theorem GlobalTheory.ThetaWeberRoad.OddDeriv.continuousAt_tailProd (τ : ℍ) (v₀ : ℂ) : ContinuousAt (tailProd τ) v₀ := by sorry
