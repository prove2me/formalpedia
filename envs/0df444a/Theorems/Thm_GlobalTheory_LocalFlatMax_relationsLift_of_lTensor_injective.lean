-- Prove2me | Theorems.Thm_GlobalTheory_LocalFlatMax_relationsLift_of_lTensor_injective
-- name    : GlobalTheory.LocalFlatMax.relationsLift_of_lTensor_injective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:14:28.414468+00:00
-- url     : https://prove2.me/theorems/76111b91-f67b-4f36-a42a-99cf3b3f062b
-- title:
--   Local Flat Max: relations Lift of l Tensor injective
-- statement:
--   The Local Flat Max construction uses the relations Lift of l Tensor injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RingHomFlatOfCompFlatOfMapMaximalIdeal.lean#L70-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RingHomFlatOfCompFlatOfMapMaximalIdeal.lean#L70-L104

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

theorem GlobalTheory.LocalFlatMax.relationsLift_of_lTensor_injective (K : Ideal A)
    (h : ∀ L : Ideal A, K ≤ L → Function.Injective (L.subtype.lTensor M)) :
    LocalFlat.RelationsLift K M := by sorry
