-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_centralBinom_le_pow_card_primes_between
-- name    : GlobalTheory.BadShare.centralBinom_le_pow_card_primes_between
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:56:53.010482+00:00
-- url     : https://prove2.me/theorems/655eb7c7-0dc5-4ea9-ae1c-eb3f457e32e3
-- title:
--   Bad Share: central Binom le pow card primes between
-- statement:
--   The Bad Share construction uses the central Binom le pow card primes between property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CentralBinomLePowCardPrimesBetween.lean#L7-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CentralBinomLePowCardPrimesBetween.lean#L7-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralBinomLePowCardPrimesBetween
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare

theorem GlobalTheory.BadShare.centralBinom_le_pow_card_primes_between (n : ℕ) (n_large : 2 < n) :
    n.centralBinom ≤ (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) *
      (2 * n) ^ ((Finset.range (2 * n + 1)).filter (fun p => p.Prime ∧ n < p)).card := by sorry
