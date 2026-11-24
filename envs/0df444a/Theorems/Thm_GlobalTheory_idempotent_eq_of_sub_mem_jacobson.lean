-- Prove2me | Theorems.Thm_GlobalTheory_idempotent_eq_of_sub_mem_jacobson
-- name    : GlobalTheory.idempotent_eq_of_sub_mem_jacobson
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:26:58.618664+00:00
-- url     : https://prove2.me/theorems/490c1956-8608-4865-b470-d745f5f48434
-- title:
--   Global Theory: idempotent eq of sub mem jacobson
-- statement:
--   The Global Theory construction uses the idempotent eq of sub mem jacobson property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L9-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L9-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open IsLocalRing Polynomial TensorProduct

theorem GlobalTheory.idempotent_eq_of_sub_mem_jacobson {S : Type*} [CommRing S] {a b : S}
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) (h : a - b ∈ (⊥ : Ideal S).jacobson) :
    a = b := by sorry
