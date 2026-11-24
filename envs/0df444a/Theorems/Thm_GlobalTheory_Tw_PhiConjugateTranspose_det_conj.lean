-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_det_conj
-- name    : GlobalTheory.Tw.PhiConjugateTranspose.det_conj
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:13:47.343619+00:00
-- url     : https://prove2.me/theorems/fb9f9774-611e-47f0-8985-4d22612e4fe5
-- title:
--   Phi Conjugate Transpose: det conj
-- statement:
--   The Phi Conjugate Transpose construction uses the det conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryTwistInvolutionGLProperties.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryTwistInvolutionGLProperties.lean#L52-L53

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

theorem GlobalTheory.Tw.PhiConjugateTranspose.det_conj (A : Matrix (Fin n) (Fin n) R) : (Phi n R * A * (Phi n R)ᵀ).det = A.det := by sorry
