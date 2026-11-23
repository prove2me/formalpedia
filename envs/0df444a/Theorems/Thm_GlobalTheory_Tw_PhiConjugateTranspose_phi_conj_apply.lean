-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_phi_conj_apply
-- name    : GlobalTheory.Tw.PhiConjugateTranspose.phi_conj_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:24:58.307953+00:00
-- url     : https://prove2.me/theorems/3789dc2b-62d5-4ca9-8de0-71d9d378ca7c
-- title:
--   Phi Conjugate Transpose: phi conj apply
-- statement:
--   The Phi Conjugate Transpose construction uses the phi conj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryTwistInvolutionGLProperties.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryTwistInvolutionGLProperties.lean#L16-L18

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

theorem GlobalTheory.Tw.PhiConjugateTranspose.phi_conj_apply (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (Phi n R * A * (Phi n R)ᵀ) i j = (-1 : R) ^ (i : ℕ) * A i.rev j.rev * (-1 : R) ^ (j : ℕ) := by sorry
