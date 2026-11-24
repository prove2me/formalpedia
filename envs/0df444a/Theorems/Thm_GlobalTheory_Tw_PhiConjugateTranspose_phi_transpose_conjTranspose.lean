-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_phi_transpose_conjTranspose
-- name    : GlobalTheory.Tw.PhiConjugateTranspose.phi_transpose_conjTranspose
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:13:47.335523+00:00
-- url     : https://prove2.me/theorems/8cefb6af-1e43-4d34-9742-4d27657d2d5e
-- title:
--   Phi Conjugate Transpose: phi transpose conj Transpose
-- statement:
--   The Phi Conjugate Transpose construction uses the phi transpose conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryTwistInvolutionGLProperties.lean#L62-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryTwistInvolutionGLProperties.lean#L62-L65

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

theorem GlobalTheory.Tw.PhiConjugateTranspose.phi_transpose_conjTranspose : ((Phi n R)ᵀ)ᴴ = Phi n R := by sorry
