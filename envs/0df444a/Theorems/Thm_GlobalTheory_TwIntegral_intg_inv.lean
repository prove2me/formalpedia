-- Prove2me | Theorems.Thm_GlobalTheory_TwIntegral_intg_inv
-- name    : GlobalTheory.TwIntegral.intg_inv
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:14:34.283485+00:00
-- url     : https://prove2.me/theorems/c56ba6e2-b68b-48fe-b29f-04e89ed4e885
-- title:
--   Tw Integral: intg inv
-- statement:
--   The Tw Integral construction uses the intg inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralTwConjMemCentMul.lean#L19-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralTwConjMemCentMul.lean#L19-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TwistedCentralizerIsNormOneTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryTwistInvolutionGLProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCommutantMulIntegralConjugate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitDiscriminantMatrixQuotientIsUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralTwConjMemCentMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Tw Matrix
open GlobalTheory GlobalTheory.TwIntegral
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}
open Matrix
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}

theorem GlobalTheory.TwIntegral.intg_inv {A : Matrix (Fin n) (Fin n) E}
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hd : ‖A.det‖ = 1) :
    ∀ i j, ‖A⁻¹ i j‖ ≤ 1 := by sorry
