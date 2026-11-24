-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_theta_isUnit
-- name    : GlobalTheory.Tw.PhiConjugateTranspose.theta_isUnit
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:13:38.785983+00:00
-- url     : https://prove2.me/theorems/df92f1ad-6ad9-4550-b8b6-d79d07920c19
-- title:
--   Phi Conjugate Transpose: theta is Unit
-- statement:
--   The Phi Conjugate Transpose construction uses the theta is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryTwistInvolutionGLProperties.lean#L83-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryTwistInvolutionGLProperties.lean#L83-L85

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryTwistInvolutionGLProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Tw Matrix
open GlobalTheory GlobalTheory.Tw GlobalTheory.Tw.PhiConjugateTranspose
variable {n : ℕ} {R : Type} [CommRing R]
variable [StarRing R]

theorem GlobalTheory.Tw.PhiConjugateTranspose.theta_isUnit {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) : IsUnit (theta g) := by sorry
