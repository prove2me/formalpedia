-- Prove2me | Theorems.Thm_GlobalTheory_finite_and_isSeparable_fractionRing_of_unramified
-- name    : GlobalTheory.finite_and_isSeparable_fractionRing_of_unramified
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:46:13.802196+00:00
-- url     : https://prove2.me/theorems/9f32e814-037b-412d-a5a1-b7fae154fcd9
-- title:
--   Global Theory: finite and is Separable fraction Ring of unramified
-- statement:
--   The Global Theory construction uses the finite and is Separable fraction Ring of unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa.lean#L385-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa.lean#L385-L396

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial IsLocalRing
open scoped TensorProduct
variable (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem GlobalTheory.finite_and_isSeparable_fractionRing_of_unramified (R B K L : Type*) [CommRing R]
    [CommRing B] [Algebra R B] [Algebra.EssFiniteType R B] [Algebra.FormallyUnramified R B]
    [Field K] [Field L] [Algebra R K] [Algebra B L] [IsFractionRing B L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [IsScalarTower R B L] :
    Module.Finite K L ∧ Algebra.IsSeparable K L := by sorry
