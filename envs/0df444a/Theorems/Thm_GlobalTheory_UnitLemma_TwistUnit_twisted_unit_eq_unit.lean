-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_TwistUnit_twisted_unit_eq_unit
-- name    : GlobalTheory.UnitLemma.TwistUnit.twisted_unit_eq_unit
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:34:08.704655+00:00
-- url     : https://prove2.me/theorems/0a6bbdc5-c110-4502-a296-73b9202c660a
-- title:
--   Twist Unit: twisted unit eq unit
-- statement:
--   The Twist Unit construction uses the twisted unit eq unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemAdjoinOfMulEqOne.lean#L115-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemAdjoinOfMulEqOne.lean#L115-L176

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitBasePointAdjoinTwistedSigmaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemAdjoinOfMulEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.TwistUnit
open GlobalTheory.UnitLemma Polynomial
variable {K : UQ}

theorem GlobalTheory.UnitLemma.TwistUnit.twisted_unit_eq_unit : ∀ (K : UQ) (B : InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable → IsIntegral K.O B.g →
    ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → ∃ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * (ε * B.g) ∧
      ∀ x : B.Aˣ, B.σ (x : B.A) = x →
        {L : Submodule K.O B.A | IsLat K.O K.E L ∧ ∀ z, z ∈ L ↔ ∀ y ∈ L,
          B.herm (β₀ * x) y z ∈ (algebraMap K.O K.E).range} = B.X x := by sorry
