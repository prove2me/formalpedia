-- Prove2me | Theorems.Thm_GlobalTheory_BI_character_eq_ind_of_imprimitive
-- name    : GlobalTheory.BI.character_eq_ind_of_imprimitive
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:58:03.590577+00:00
-- url     : https://prove2.me/theorems/31c2c661-02ac-4a2e-9331-8e1914bfd2a5
-- title:
--   BI: character eq ind of imprimitive
-- statement:
--   The BI construction uses the character eq ind of imprimitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CharacterEqInducedOfImprimitivitySystem.lean#L10-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CharacterEqInducedOfImprimitivitySystem.lean#L10-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharTraceMulIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SumConjIdempotentEqCardSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharacterEqInducedOfImprimitivitySystem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
open GlobalTheory GlobalTheory.BI

theorem GlobalTheory.BI.character_eq_ind_of_imprimitive :
    ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] (ρ : Representation L G V) (T : Subgroup G) (e : Module.End L V), ρ.IsIrreducible → e ≠ 0 → e * e = e → (∀ t ∈ T, ρ t * e = e * ρ t) → (∀ g ∉ T, e * ρ g * e = 0) → ∃ ψ : T → L, IsChar L L ψ ∧ ∀ g, ρ.character g = ind T ψ g := by sorry
