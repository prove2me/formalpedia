-- Prove2me | Theorems.Thm_GlobalTheory_card_fixedBy_quotient_eq_relIndex_of_pRegular
-- name    : GlobalTheory.card_fixedBy_quotient_eq_relIndex_of_pRegular
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:07:02.940787+00:00
-- url     : https://prove2.me/theorems/8e216270-7a25-4cbe-a5d6-6b28d769612c
-- title:
--   Global Theory: card fixed By quotient eq rel Index of p Regular
-- statement:
--   The Global Theory construction uses the card fixed By quotient eq rel Index of p Regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CardFixedByQuotientEqRelIndexOfPRegular.lean#L20-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CardFixedByQuotientEqRelIndexOfPRegular.lean#L20-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardFixedByQuotientEqRelIndexOfPRegular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.card_fixedBy_quotient_eq_relIndex_of_pRegular :
    ∀ (G : Type) [Group G] [Finite G] (c : G) (p : ℕ) (H N : Subgroup G), Nat.Coprime (orderOf c) p → Subgroup.zpowers c ≤ H → (∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ Subgroup.zpowers c) → (∀ g : G, g ∈ N ↔ ∀ d ∈ Subgroup.zpowers c, g * d * g⁻¹ ∈ Subgroup.zpowers c) → Nat.card (MulAction.fixedBy (G ⧸ H) c) = H.relIndex N := by sorry
