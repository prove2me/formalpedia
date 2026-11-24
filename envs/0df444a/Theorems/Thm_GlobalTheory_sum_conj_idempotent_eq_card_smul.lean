-- Prove2me | Theorems.Thm_GlobalTheory_sum_conj_idempotent_eq_card_smul
-- name    : GlobalTheory.sum_conj_idempotent_eq_card_smul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:22:55.346522+00:00
-- url     : https://prove2.me/theorems/06dc4ee0-4d2f-4950-96e4-d633414cdb0d
-- title:
--   Global Theory: sum conj idempotent eq card smul
-- statement:
--   The Global Theory construction uses the sum conj idempotent eq card smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/SumConjIdempotentEqCardSmul.lean#L5-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/SumConjIdempotentEqCardSmul.lean#L5-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SumConjIdempotentEqCardSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.sum_conj_idempotent_eq_card_smul (L : Type) [Field L] (G : Type) [Group G] [Fintype G]
    (V : Type) [AddCommGroup V] [Module L V] (ρ : Representation L G V) (T : Subgroup G)
    (e : Module.End L V) (hirr : ρ.IsIrreducible) (he0 : e ≠ 0) (hee : e * e = e)
    (hT : ∀ t ∈ T, ρ t * e = e * ρ t) (hoff : ∀ g ∉ T, e * ρ g * e = 0) :
    ∑ x : G, ρ x * e * ρ x⁻¹ = (Nat.card T : L) • (1 : Module.End L V) := by sorry
