-- Prove2me | Theorems.Thm_GlobalTheory_T_ncard_primitive_tuples_gram_mod_nilpotent
-- name    : GlobalTheory.T.ncard_primitive_tuples_gram_mod_nilpotent
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:45:51.01187+00:00
-- url     : https://prove2.me/theorems/6b4eb957-ab6a-5644-b656-b20a8d2a5d64
-- title:
--   T: ncard primitive tuples gram mod nilpotent
-- statement:
--   The T construction uses the ncard primitive tuples gram mod nilpotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NcardPrimitiveTuplesGramModNilpotentStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NcardPrimitiveTuplesGramModNilpotentStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardPrimitiveTuplesGramModNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardPrimitiveTuplesGramModNilpotentStatement
import Theorems.Thm_GlobalTheory_GramCount_Prim_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.ncard_primitive_tuples_gram_mod_nilpotent : ∀ {A B : Type} [CommRing A] [Finite A] [CommRing B] (c : A →+* A) (c' : B →+* B), (∀ u, c (c u) = u) → ∀ (p : A), IsNilpotent p → ∀ (φ : A →+* B), Function.Surjective φ → (∀ u, φ (c u) = c' (φ u)) → (∀ u, φ u = 0 ↔ p ∣ u) → ∀ (m n : ℕ) (G : Matrix (Fin m) (Fin m) A), Set.ncard {x : Fin m → Fin n → A | Prim c x ∧ ∀ a b, p ∣ ip c (x b) (x a) - G a b} = Nat.card {u : A // p ∣ u} ^ (n * m) * Set.ncard (sols c' n (G.map φ)) := by sorry
