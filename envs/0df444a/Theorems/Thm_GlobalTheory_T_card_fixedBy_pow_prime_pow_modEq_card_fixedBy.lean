-- Prove2me | Theorems.Thm_GlobalTheory_T_card_fixedBy_pow_prime_pow_modEq_card_fixedBy
-- name    : GlobalTheory.T.card_fixedBy_pow_prime_pow_modEq_card_fixedBy
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:27:59.772743+00:00
-- url     : https://prove2.me/theorems/4299949a-5a1f-4a7c-9102-549a0c619030
-- title:
--   T: card fixed By pow prime pow mod Eq card fixed By
-- statement:
--   The T construction uses the card fixed By pow prime pow mod Eq card fixed By property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CardFixedByPowPrimePowModEqStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CardFixedByPowPrimePowModEqStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardFixedByPowPrimePowModEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardFixedByPowPrimePowModEqStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.card_fixedBy_pow_prime_pow_modEq_card_fixedBy : ∀ (G : Type) [Group G] (X : Type) [Finite X] [MulAction G X] (x : G) (p k : ℕ), p.Prime → Nat.card (MulAction.fixedBy X (x ^ p ^ k)) ≡ Nat.card (MulAction.fixedBy X x) [MOD p] := by sorry
