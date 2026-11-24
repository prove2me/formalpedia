-- Prove2me | Theorems.Thm_GlobalTheory_T_idempotent_eq_one_and_character_eq_of_isIrreducible
-- name    : GlobalTheory.T.idempotent_eq_one_and_character_eq_of_isIrreducible
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:46:48.873748+00:00
-- url     : https://prove2.me/theorems/b67aff41-062b-4ac3-9569-a6cf7176e66f
-- title:
--   T: idempotent eq one and character eq of is Irreducible
-- statement:
--   The T construction uses the idempotent eq one and character eq of is Irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IrreducibleIdempotentEqOneAndCharacterEqWeightAlStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IrreducibleIdempotentEqOneAndCharacterEqWeightAlStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleIdempotentEqOneAndCharacterEqWeightAl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleIdempotentEqOneAndCharacterEqWeightAlStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.idempotent_eq_one_and_character_eq_of_isIrreducible : ∀ (L : Type) [Field L] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] (ρ : Representation L G V), ρ.IsIrreducible → (∀ e : Module.End L V, e ≠ 0 → e * e = e → (∀ g, ρ g * e = e * ρ g) → e = 1) ∧ (∀ (lam : G →* Lˣ) (v : V), v ≠ 0 → (∀ g, ρ g v = (lam g : L) • v) → ∀ g, ρ.character g = (lam g : L)) := by sorry
