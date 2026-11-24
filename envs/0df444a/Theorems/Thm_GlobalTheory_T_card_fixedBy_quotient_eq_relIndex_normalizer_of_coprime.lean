-- Prove2me | Theorems.Thm_GlobalTheory_T_card_fixedBy_quotient_eq_relIndex_normalizer_of_coprime
-- name    : GlobalTheory.T.card_fixedBy_quotient_eq_relIndex_normalizer_of_coprime
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:28:18.095798+00:00
-- url     : https://prove2.me/theorems/470ad403-dec1-45d3-8f55-f030914efc3e
-- title:
--   T: card fixed By quotient eq rel Index normalizer of coprime
-- statement:
--   The T construction uses the card fixed By quotient eq rel Index normalizer of coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CardFixedByQuotientEqRelIndexOfPRegularStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CardFixedByQuotientEqRelIndexOfPRegularStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardFixedByQuotientEqRelIndexOfPRegular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardFixedByQuotientEqRelIndexOfPRegularStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.card_fixedBy_quotient_eq_relIndex_normalizer_of_coprime : ∀ (G : Type) [Group G] [Finite G] (c : G) (p : ℕ) (H N : Subgroup G), Nat.Coprime (orderOf c) p → Subgroup.zpowers c ≤ H → (∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ Subgroup.zpowers c) → (∀ g : G, g ∈ N ↔ ∀ d ∈ Subgroup.zpowers c, g * d * g⁻¹ ∈ Subgroup.zpowers c) → Nat.card (MulAction.fixedBy (G ⧸ H) c) = H.relIndex N := by sorry
