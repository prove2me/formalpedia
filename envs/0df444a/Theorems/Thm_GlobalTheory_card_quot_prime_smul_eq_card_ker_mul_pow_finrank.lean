-- Prove2me | Theorems.Thm_GlobalTheory_card_quot_prime_smul_eq_card_ker_mul_pow_finrank
-- name    : GlobalTheory.card_quot_prime_smul_eq_card_ker_mul_pow_finrank
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:07:41.748224+00:00
-- url     : https://prove2.me/theorems/4bef66c5-5116-43a3-aecd-3a5ae51b1169
-- title:
--   Global Theory: card quot prime smul eq card ker mul pow finrank
-- statement:
--   The Global Theory construction uses the card quot prime smul eq card ker mul pow finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardQuotPrimeSmulEqCardKerMulPowFinrank.lean#L93-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardQuotPrimeSmulEqCardKerMulPowFinrank.lean#L93-L106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardQuotPrimeSmulEqCardKerMulPowFinrank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
open GlobalTheory

theorem GlobalTheory.card_quot_prime_smul_eq_card_ker_mul_pow_finrank (M : Type) [AddCommGroup M]
    [inst : Module ℤ M] [Module.Finite ℤ M] (p : ℕ) [Fact p.Prime] :
    Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) =
      Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) *
        p ^ Module.finrank ℤ M := by sorry
