-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_TwistUnitAny_stable_of_unimodular
-- name    : GlobalTheory.UnitLemma.TwistUnitAny.stable_of_unimodular
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:34:56.39626+00:00
-- url     : https://prove2.me/theorems/374ac44f-20f7-4039-8be7-c0d4efe6350b
-- title:
--   Twist Unit Any: stable of unimodular
-- statement:
--   The Twist Unit Any construction uses the stable of unimodular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsBasePointTwistedHermUnimodularEqSelfDual.lean#L13-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsBasePointTwistedHermUnimodularEqSelfDual.lean#L13-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemAdjoinOfMulEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitSigmaEqMulHilbert90InvAlg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KappaSumZeroAndStableSumMulZeroOfNotIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasePointTwistedHermUnimodularEqSelfDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.TwistUnitAny
open GlobalTheory.UnitLemma Polynomial
variable {K : UQ}

theorem GlobalTheory.UnitLemma.TwistUnitAny.stable_of_unimodular (B : InvAlg K) (hg : B.g * B.σ B.g = 1) (ε : B.A) (hε : ε = 1 ∨ ε = -1)
    (β x : B.A) (hβ : B.σ β = β * (ε * B.g)) (hx : B.σ x = x) (L : Submodule K.O B.A)
    (hU : ∀ z, z ∈ L ↔ ∀ y ∈ L, B.herm (β * x) y z ∈ (algebraMap K.O K.E).range) :
    ∀ y ∈ L, B.g * y ∈ L := by sorry
