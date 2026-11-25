-- Prove2me | Theorems.Thm_GlobalTheory_TeichPair_exists_seq
-- name    : GlobalTheory.TeichPair.exists_seq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:34:28.355799+00:00
-- url     : https://prove2.me/theorems/83eff773-a315-4137-8a09-cc2d5d6f184a
-- title:
--   Teich Pair: exists seq
-- statement:
--   The Teich Pair construction uses the exists seq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EqZeroOfGe.lean#L132-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EqZeroOfGe.lean#L132-L254

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EqZeroOfGe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.TeichPair
variable {C : Type} [Field C]

theorem GlobalTheory.TeichPair.exists_seq (V : VF C) (cpl : ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n))
    {O : Type} [CommRing O] {d : ℕ} [NeZero d] (e : ZMod d → O →+* C) (hint : ∀ a x, V.Ge 0 (e a x))
    (hfrob : ∀ a x, V.MM (e (a + 1) x - e a x ^ V.l))
    (hsep : ∀ a a', a ≠ a' → ∃ x, V.v (e a x - e a' x) = 0)
    (hunr : ∃ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) ∧ (∀ a, V.MM (e a ε - 1)) ∧
      ∀ x : O, (∀ a, V.MM (e a x)) → ∃ y, ε * x = (V.l : O) * y) :
    ∃ (s : ℕ → O) (N : ℕ) (ζ : ZMod d → C), (∀ n, ∃ y, s (n + 1) - s n = (V.l : O) ^ n * y) ∧ V.v (N : C) = 0 ∧
      (∀ a, ζ a ^ N = 1) ∧ Function.Injective ζ ∧ (∀ a, ζ (a + 1) = ζ a ^ V.l) ∧
      ∀ a (n : ℕ), V.Ge n (ζ a - e a (s n)) := by sorry
