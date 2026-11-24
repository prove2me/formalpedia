-- Prove2me | Theorems.Thm_GlobalTheory_exists_mem_pow_sub_mem_pow_succ_facts_exists_mem_pow_sub_mem_pow_succ
-- name    : GlobalTheory.exists_mem_pow_sub_mem_pow_succ_facts.exists_mem_pow_sub_mem_pow_succ
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:34:24.775094+00:00
-- url     : https://prove2.me/theorems/d5a877ae-1f97-4c7c-9212-5499a336f7e8
-- title:
--   exists mem pow sub mem pow succ facts: exists mem pow sub mem pow succ
-- statement:
--   The exists mem pow sub mem pow succ facts construction uses the exists mem pow sub mem pow succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsMemPowSubMemPowSucc.lean#L7-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsMemPowSubMemPowSucc.lean#L7-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.exists_mem_pow_sub_mem_pow_succ_facts

theorem GlobalTheory.exists_mem_pow_sub_mem_pow_succ_facts.exists_mem_pow_sub_mem_pow_succ {A : Type u_1} [CommRing A] {B : Type u_2} [CommRing B]
    {φ : A →+* B} {I : Ideal A} {J : Ideal B} (hIJ : I ≤ Ideal.comap φ J)
    (h0 : ∀ b : B, ∃ a : A, φ a - b ∈ J)
    (h1 : ∀ y ∈ J, ∃ x ∈ I, φ x - y ∈ J ^ (2 : ℕ)) (n : ℕ) :
    ∀ y ∈ J ^ n, ∃ x ∈ I ^ n, φ x - y ∈ J ^ (n + (1 : ℕ)) := by sorry
