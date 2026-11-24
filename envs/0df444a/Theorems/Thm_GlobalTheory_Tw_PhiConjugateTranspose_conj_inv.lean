-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_conj_inv
-- name    : GlobalTheory.Tw.PhiConjugateTranspose.conj_inv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:13:25.165909+00:00
-- url     : https://prove2.me/theorems/b000a961-ba9f-48af-b2d2-bcd8da76b7ff
-- title:
--   Phi Conjugate Transpose: conj inv
-- statement:
--   The Phi Conjugate Transpose construction uses the conj inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryTwistInvolutionGLProperties.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryTwistInvolutionGLProperties.lean#L48-L50

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

theorem GlobalTheory.Tw.PhiConjugateTranspose.conj_inv (A : Matrix (Fin n) (Fin n) R) :
    (Phi n R * A * (Phi n R)ᵀ)⁻¹ = Phi n R * A⁻¹ * (Phi n R)ᵀ := by sorry
