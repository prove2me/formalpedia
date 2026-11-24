-- Prove2me | Theorems.Thm_GlobalTheory_T_card_zmod_tensor_eq_card_quot_prime_multiples
-- name    : GlobalTheory.T.card_zmod_tensor_eq_card_quot_prime_multiples
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:27:31.105805+00:00
-- url     : https://prove2.me/theorems/7bdd04e1-867f-40b2-bbd8-e10b0d78f328
-- title:
--   T: card zmod tensor eq card quot prime multiples
-- statement:
--   The T construction uses the card zmod tensor eq card quot prime multiples property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardZmodTensorEqCardQuotPrimeMultiplesStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardZmodTensorEqCardQuotPrimeMultiplesStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardZmodTensorEqCardQuotPrimeMultiples
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardZmodTensorEqCardQuotPrimeMultiplesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.card_zmod_tensor_eq_card_quot_prime_multiples : ∀ (M : Type) [AddCommGroup M] [Module ℤ M] (p : ℕ), Nat.card (TensorProduct ℤ (ZMod p) M) = Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) := by sorry
