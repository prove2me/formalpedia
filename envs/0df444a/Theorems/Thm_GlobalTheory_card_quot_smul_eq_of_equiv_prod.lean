-- Prove2me | Theorems.Thm_GlobalTheory_card_quot_smul_eq_of_equiv_prod
-- name    : GlobalTheory.card_quot_smul_eq_of_equiv_prod
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:07:53.436613+00:00
-- url     : https://prove2.me/theorems/5a8eea1b-3077-47ab-b7ad-d9338d69d182
-- title:
--   Global Theory: card quot smul eq of equiv prod
-- statement:
--   The Global Theory construction uses the card quot smul eq of equiv prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardQuotPrimeSmulEqCardKerMulPowFinrank.lean#L15-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardQuotPrimeSmulEqCardKerMulPowFinrank.lean#L15-L91

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

theorem GlobalTheory.card_quot_smul_eq_of_equiv_prod {M D : Type} [AddCommGroup M] [AddCommGroup D] [Finite D]
    {n : ℕ} (e : M ≃+ (Fin n → ℤ) × D) (p : ℕ) (hp : p ≠ 0) :
    Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) =
      Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) *
        p ^ Module.finrank ℤ M := by sorry
