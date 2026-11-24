-- Prove2me | Theorems.Thm_GlobalTheory_one_sub_mem_iff_notMem_of_isIdempotentElem
-- name    : GlobalTheory.one_sub_mem_iff_notMem_of_isIdempotentElem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:26:53.781252+00:00
-- url     : https://prove2.me/theorems/25d70003-8da6-443c-9c52-e80365820f2d
-- title:
--   Global Theory: one sub mem iff not Mem of is Idempotent Elem
-- statement:
--   The Global Theory construction uses the one sub mem iff not Mem of is Idempotent Elem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L161-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L161-L166

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

theorem GlobalTheory.one_sub_mem_iff_notMem_of_isIdempotentElem {S : Type*} [CommRing S] {e : S}
    (he : IsIdempotentElem e) (n : Ideal S) [hn : n.IsPrime] : 1 - e ∈ n ↔ e ∉ n := by sorry
