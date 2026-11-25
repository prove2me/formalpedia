-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_PrincipalLat_eq_mulLat_integralClosure
-- name    : GlobalTheory.UnitLemma.PrincipalLat.eq_mulLat_integralClosure
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:05:34.226496+00:00
-- url     : https://prove2.me/theorems/e338ca12-f8f1-49ce-97e9-f319b0629633
-- title:
--   Principal Lat: eq mul Lat integral Closure
-- statement:
--   The Principal Lat construction uses the eq mul Lat integral Closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqMulIntegralClosureOfSeparableInvolutionAlgebra.lean#L161-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqMulIntegralClosureOfSeparableInvolutionAlgebra.lean#L161-L167

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

theorem GlobalTheory.UnitLemma.PrincipalLat.eq_mulLat_integralClosure : ∀ (K : UQ) (B : InvAlg K), B.P.Separable →
    ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) →
    ∃ a : B.Aˣ, J = mulLat K.O (a : B.A) (Subalgebra.toSubmodule (integralClosure K.O B.A)) := by sorry
