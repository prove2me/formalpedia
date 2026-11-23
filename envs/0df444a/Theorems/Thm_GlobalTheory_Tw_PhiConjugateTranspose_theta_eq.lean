-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_theta_eq
-- name    : GlobalTheory.Tw.PhiConjugateTranspose.theta_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:24:58.887399+00:00
-- url     : https://prove2.me/theorems/4f47d45a-ee4f-4d12-81c0-d22df360d5b6
-- title:
--   Phi Conjugate Transpose: theta eq
-- statement:
--   The Phi Conjugate Transpose construction uses the theta eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryTwistInvolutionGLProperties.lean#L71-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryTwistInvolutionGLProperties.lean#L71-L71

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

theorem GlobalTheory.Tw.PhiConjugateTranspose.theta_eq (g : Matrix (Fin n) (Fin n) R) : theta g = Phi n R * (g⁻¹)ᴴ * (Phi n R)ᵀ := by sorry
