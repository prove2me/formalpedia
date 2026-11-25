-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_inv_log_le_sum_inv_primes_between
-- name    : GlobalTheory.BadShare.inv_log_le_sum_inv_primes_between
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:59:07.151825+00:00
-- url     : https://prove2.me/theorems/50409e1e-79ee-4d33-a9f3-7c5ca4bc1c19
-- title:
--   Bad Share: inv log le sum inv primes between
-- statement:
--   The Bad Share construction uses the inv log le sum inv primes between property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CentralBinomLePowCardPrimesBetween.lean#L150-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CentralBinomLePowCardPrimesBetween.lean#L150-L259

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
open Polynomial Classical

theorem GlobalTheory.BadShare.inv_log_le_sum_inv_primes_between :
    ∀ N : ℕ, 100000 ≤ N → 1 / (10 * Real.log N) ≤
      ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N),
        (1 : ℝ) / p := by sorry
