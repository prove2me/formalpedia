-- Prove2me | Theorems.Thm_GlobalTheory_LocalFlatMax_lTensor_injective_of_smul_le
-- name    : GlobalTheory.LocalFlatMax.lTensor_injective_of_smul_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:14:04.532798+00:00
-- url     : https://prove2.me/theorems/9744ef5c-19f8-40ca-b86a-b7841c03a3b4
-- title:
--   Local Flat Max: l Tensor injective of smul le
-- statement:
--   The Local Flat Max construction uses the l Tensor injective of smul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RingHomFlatOfCompFlatOfMapMaximalIdeal.lean#L14-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RingHomFlatOfCompFlatOfMapMaximalIdeal.lean#L14-L48

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

theorem GlobalTheory.LocalFlatMax.lTensor_injective_of_smul_le (I : Ideal A) [hI : I.IsMaximal]
    (h : Function.Injective (I.subtype.lTensor M))
    {F : Type u} [AddCommGroup F] [Module A F] (N : Submodule A F)
    (hN : I • (⊤ : Submodule A F) ≤ N) : Function.Injective (N.subtype.lTensor M) := by sorry
