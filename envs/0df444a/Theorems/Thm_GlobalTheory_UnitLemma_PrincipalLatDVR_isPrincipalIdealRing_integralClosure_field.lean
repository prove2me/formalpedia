-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_PrincipalLatDVR_isPrincipalIdealRing_integralClosure_field
-- name    : GlobalTheory.UnitLemma.PrincipalLatDVR.isPrincipalIdealRing_integralClosure_field
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:10:07.365842+00:00
-- url     : https://prove2.me/theorems/0e79b7fd-b9bb-4176-b164-551731d238c9
-- title:
--   Principal Lat DVR: is Principal Ideal Ring integral Closure field
-- statement:
--   The Principal Lat DVR construction uses the is Principal Ideal Ring integral Closure field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqSubmoduleMulLeftImageIntegralClosureOfSeparabl.lean#L35-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqSubmoduleMulLeftImageIntegralClosureOfSeparabl.lean#L35-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqMulIntegralClosureOfSeparableInvolutionAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfCharpolySeparableInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CharpolyDvdPowFinrankOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqSubmoduleMulLeftImageIntegralClosureOfSeparabl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.PrincipalLatDVR

theorem GlobalTheory.UnitLemma.PrincipalLatDVR.isPrincipalIdealRing_integralClosure_field {O E L : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [Field L]
    [Algebra E L] [Algebra O L] [IsScalarTower O E L] [FiniteDimensional E L] :
    IsPrincipalIdealRing (integralClosure O L) := by sorry
