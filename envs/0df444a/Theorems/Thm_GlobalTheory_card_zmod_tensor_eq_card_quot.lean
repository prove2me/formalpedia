-- Prove2me | Theorems.Thm_GlobalTheory_card_zmod_tensor_eq_card_quot
-- name    : GlobalTheory.card_zmod_tensor_eq_card_quot
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:07:57.432127+00:00
-- url     : https://prove2.me/theorems/f8caa4b6-4f38-4f3e-9e3b-4c2412969540
-- title:
--   Global Theory: card zmod tensor eq card quot
-- statement:
--   The Global Theory construction uses the card zmod tensor eq card quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardZmodTensorEqCardQuotPrimeMultiples.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardZmodTensorEqCardQuotPrimeMultiples.lean#L18-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardZmodTensorEqCardQuotPrimeMultiples
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

theorem GlobalTheory.card_zmod_tensor_eq_card_quot (M : Type) [AddCommGroup M] [Module ℤ M] (p : ℕ) :
    Nat.card (TensorProduct ℤ (ZMod p) M) =
      Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) := by sorry
