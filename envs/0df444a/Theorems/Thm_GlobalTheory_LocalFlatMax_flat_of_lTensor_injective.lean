-- Prove2me | Theorems.Thm_GlobalTheory_LocalFlatMax_flat_of_lTensor_injective
-- name    : GlobalTheory.LocalFlatMax.flat_of_lTensor_injective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:13:58.722305+00:00
-- url     : https://prove2.me/theorems/063d011f-748d-41dd-8831-5cfbc23ed915
-- title:
--   Local Flat Max: flat of l Tensor injective
-- statement:
--   The Local Flat Max construction uses the flat of l Tensor injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RingHomFlatOfCompFlatOfMapMaximalIdeal.lean#L106-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RingHomFlatOfCompFlatOfMapMaximalIdeal.lean#L106-L112

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RingHomFlatOfCompFlatOfMapMaximalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap IsLocalRing
open GlobalTheory
open GlobalTheory.LocalFlatMax
universe u
variable {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M]

theorem GlobalTheory.LocalFlatMax.flat_of_lTensor_injective [IsNoetherianRing A] (B : Type*) [CommRing B] [Algebra A B]
    [IsNoetherianRing B] [Module B M] [IsScalarTower A B M] [Module.Finite B M] (I : Ideal A)
    [I.IsMaximal] (hI : I.map (algebraMap A B) ≤ Ideal.jacobson ⊥)
    (h : Function.Injective (I.subtype.lTensor M)) : Module.Flat A M := by sorry
