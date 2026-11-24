-- Prove2me | Theorems.Thm_GlobalTheory_TwIntegral_isUnit_of_norm_det
-- name    : GlobalTheory.TwIntegral.isUnit_of_norm_det
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:13:58.460647+00:00
-- url     : https://prove2.me/theorems/8aec2860-74ab-4e64-8b12-17f56d9f424c
-- title:
--   Tw Integral: is Unit of norm det
-- statement:
--   The Tw Integral construction uses the is Unit of norm det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralTwConjMemCentMul.lean#L41-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralTwConjMemCentMul.lean#L41-L46

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

theorem GlobalTheory.TwIntegral.isUnit_of_norm_det {A : Matrix (Fin n) (Fin n) E} (hd : ‖A.det‖ = 1) :
    IsUnit A := by sorry
