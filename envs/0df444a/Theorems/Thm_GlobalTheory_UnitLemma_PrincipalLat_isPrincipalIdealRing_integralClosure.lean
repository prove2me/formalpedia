-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_PrincipalLat_isPrincipalIdealRing_integralClosure
-- name    : GlobalTheory.UnitLemma.PrincipalLat.isPrincipalIdealRing_integralClosure
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:05:42.762571+00:00
-- url     : https://prove2.me/theorems/ba0701d1-3609-441f-a9b1-fab15946135d
-- title:
--   Principal Lat: is Principal Ideal Ring integral Closure
-- statement:
--   The Principal Lat construction uses the is Principal Ideal Ring integral Closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqMulIntegralClosureOfSeparableInvolutionAlgebra.lean#L129-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqMulIntegralClosureOfSeparableInvolutionAlgebra.lean#L129-L159

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqMulIntegralClosureOfSeparableInvolutionAlgebra
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
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.PrincipalLat

theorem GlobalTheory.UnitLemma.PrincipalLat.isPrincipalIdealRing_integralClosure {O E A : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field E]
    [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra E A] [Algebra O A]
    [IsScalarTower O E A] [Module.Finite E A] [IsReduced A] :
    IsPrincipalIdealRing (integralClosure O A) := by sorry
