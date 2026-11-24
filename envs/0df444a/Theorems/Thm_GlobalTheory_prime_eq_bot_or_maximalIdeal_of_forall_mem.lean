-- Prove2me | Theorems.Thm_GlobalTheory_prime_eq_bot_or_maximalIdeal_of_forall_mem
-- name    : GlobalTheory.prime_eq_bot_or_maximalIdeal_of_forall_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:15:22.373955+00:00
-- url     : https://prove2.me/theorems/69190e3c-016d-4e44-b494-c90b88a299d0
-- title:
--   Global Theory: prime eq bot or maximal Ideal of forall mem
-- statement:
--   The Global Theory construction uses the prime eq bot or maximal Ideal of forall mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PrimeEqBotOrMaximalIdealOfIsFieldAway.lean#L13-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PrimeEqBotOrMaximalIdealOfIsFieldAway.lean#L13-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimeEqBotOrMaximalIdealOfIsFieldAway
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing
variable {B : Type*} [CommRing B] [IsDomain B]
variable [IsNoetherianRing B] [IsLocalRing B]

theorem GlobalTheory.prime_eq_bot_or_maximalIdeal_of_forall_mem {f : B} (hf : f ≠ 0)
    (H : ∀ p : Ideal B, p.IsPrime → p ≠ ⊥ → f ∈ p) {p : Ideal B} (hp : p.IsPrime) :
    p = ⊥ ∨ p = maximalIdeal B := by sorry
