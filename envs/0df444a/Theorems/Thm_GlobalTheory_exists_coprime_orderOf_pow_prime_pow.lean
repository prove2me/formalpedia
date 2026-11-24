-- Prove2me | Theorems.Thm_GlobalTheory_exists_coprime_orderOf_pow_prime_pow
-- name    : GlobalTheory.exists_coprime_orderOf_pow_prime_pow
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:30:39.697829+00:00
-- url     : https://prove2.me/theorems/a8597988-8d34-4040-b884-0700a76a94fc
-- title:
--   Global Theory: exists coprime order Of pow prime pow
-- statement:
--   The Global Theory construction uses the exists coprime order Of pow prime pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsCoprimeOrderOfPowPrimePow.lean#L5-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsCoprimeOrderOfPowPrimePow.lean#L5-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsCoprimeOrderOfPowPrimePow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_coprime_orderOf_pow_prime_pow (G : Type) [Group G] [Finite G] (x : G) (p : ℕ)
    (hp : p.Prime) : ∃ k : ℕ, Nat.Coprime (orderOf (x ^ p ^ k)) p := by sorry
