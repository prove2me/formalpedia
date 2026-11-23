-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_phi_apply
-- name    : GlobalTheory.Tw.PhiConjugateTranspose.phi_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:12.788051+00:00
-- url     : https://prove2.me/theorems/d65ac3ff-52a7-4d52-948f-98adc60390ab
-- title:
--   Phi Conjugate Transpose: phi apply
-- statement:
--   The Phi Conjugate Transpose construction uses the phi apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryTwistInvolutionGLProperties.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryTwistInvolutionGLProperties.lean#L9-L14

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

theorem GlobalTheory.Tw.PhiConjugateTranspose.phi_apply (i k : Fin n) : Phi n R i k = if k = i.rev then (-1 : R) ^ (i : ℕ) else 0 := by sorry
