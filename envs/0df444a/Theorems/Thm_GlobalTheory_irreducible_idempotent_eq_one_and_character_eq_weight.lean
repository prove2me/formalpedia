-- Prove2me | Theorems.Thm_GlobalTheory_irreducible_idempotent_eq_one_and_character_eq_weight
-- name    : GlobalTheory.irreducible_idempotent_eq_one_and_character_eq_weight
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:56:01.764058+00:00
-- url     : https://prove2.me/theorems/412e6965-5288-428a-bbd6-c9edaa45a387
-- title:
--   Global Theory: irreducible idempotent eq one and character eq weight
-- statement:
--   The Global Theory construction uses the irreducible idempotent eq one and character eq weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IrreducibleIdempotentEqOneAndCharacterEqWeightAl.lean#L5-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IrreducibleIdempotentEqOneAndCharacterEqWeightAl.lean#L5-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleIdempotentEqOneAndCharacterEqWeightAl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.irreducible_idempotent_eq_one_and_character_eq_weight
    (L : Type) [Field L] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] (ρ : Representation L G V) (hρ : ρ.IsIrreducible) :
    (∀ e : Module.End L V, e ≠ 0 → e * e = e → (∀ g, ρ g * e = e * ρ g) → e = 1) ∧
    (∀ (lam : G →* Lˣ) (v : V), v ≠ 0 → (∀ g, ρ g v = (lam g : L) • v) →
      ∀ g, ρ.character g = (lam g : L)) := by sorry
