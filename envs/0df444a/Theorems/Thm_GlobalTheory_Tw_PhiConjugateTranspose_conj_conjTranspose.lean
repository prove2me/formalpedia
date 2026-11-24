-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_conj_conjTranspose
-- name    : GlobalTheory.Tw.PhiConjugateTranspose.conj_conjTranspose
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:13:19.551796+00:00
-- url     : https://prove2.me/theorems/88ffd171-58dc-4d28-bbe1-aa3965e78163
-- title:
--   Phi Conjugate Transpose: conj conj Transpose
-- statement:
--   The Phi Conjugate Transpose construction uses the conj conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryTwistInvolutionGLProperties.lean#L67-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryTwistInvolutionGLProperties.lean#L67-L69

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

theorem GlobalTheory.Tw.PhiConjugateTranspose.conj_conjTranspose (A : Matrix (Fin n) (Fin n) R) :
    (Phi n R * A * (Phi n R)ᵀ)ᴴ = Phi n R * Aᴴ * (Phi n R)ᵀ := by sorry
