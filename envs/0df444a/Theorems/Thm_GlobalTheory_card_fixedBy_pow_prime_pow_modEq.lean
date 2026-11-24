-- Prove2me | Theorems.Thm_GlobalTheory_card_fixedBy_pow_prime_pow_modEq
-- name    : GlobalTheory.card_fixedBy_pow_prime_pow_modEq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:06:55.646747+00:00
-- url     : https://prove2.me/theorems/e314e7fe-4e69-463c-b721-99df7b529e58
-- title:
--   Global Theory: card fixed By pow prime pow mod Eq
-- statement:
--   The Global Theory construction uses the card fixed By pow prime pow mod Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CardFixedByPowPrimePowModEq.lean#L5-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CardFixedByPowPrimePowModEq.lean#L5-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardFixedByPowPrimePowModEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.card_fixedBy_pow_prime_pow_modEq (G : Type) [Group G] (X : Type) [Finite X] [MulAction G X]
    (x : G) (p k : ℕ) (hp : p.Prime) :
    Nat.card (MulAction.fixedBy X (x ^ p ^ k)) ≡ Nat.card (MulAction.fixedBy X x) [MOD p] := by sorry
