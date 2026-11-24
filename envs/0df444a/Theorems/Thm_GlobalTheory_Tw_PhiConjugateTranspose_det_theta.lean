-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_det_theta
-- name    : GlobalTheory.Tw.PhiConjugateTranspose.det_theta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:07.198106+00:00
-- url     : https://prove2.me/theorems/4050e588-2076-475f-a6d0-df53c6ee524d
-- title:
--   Phi Conjugate Transpose: det theta
-- statement:
--   The Phi Conjugate Transpose construction uses the det theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryTwistInvolutionGLProperties.lean#L80-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryTwistInvolutionGLProperties.lean#L80-L81

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

theorem GlobalTheory.Tw.PhiConjugateTranspose.det_theta (g : Matrix (Fin n) (Fin n) R) : (theta g).det = star (g⁻¹).det := by sorry
