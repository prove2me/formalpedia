-- Prove2me | Theorems.Thm_GlobalTheory_conj_mem_zpowers_of_mem_of_pRegular
-- name    : GlobalTheory.conj_mem_zpowers_of_mem_of_pRegular
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:13:25.759119+00:00
-- url     : https://prove2.me/theorems/e84f5d2e-c7a4-4c5f-9e78-254f12d34fff
-- title:
--   Global Theory: conj mem zpowers of mem of p Regular
-- statement:
--   The Global Theory construction uses the conj mem zpowers of mem of p Regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CardFixedByQuotientEqRelIndexOfPRegular.lean#L5-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CardFixedByQuotientEqRelIndexOfPRegular.lean#L5-L18

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

theorem GlobalTheory.conj_mem_zpowers_of_mem_of_pRegular {G : Type} [Group G] (c : G) (p : ℕ) (H : Subgroup G)
    (hc : Nat.Coprime (orderOf c) p)
    (hp : ∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ Subgroup.zpowers c) (g : G)
    (hg : g⁻¹ * c * g ∈ H) : g⁻¹ * c * g ∈ Subgroup.zpowers c := by sorry
