-- Prove2me | Theorems.Thm_GlobalTheory_TeichPair_exists_sep
-- name    : GlobalTheory.TeichPair.exists_sep
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:15:35.65042+00:00
-- url     : https://prove2.me/theorems/85a5cc1a-1ee9-48a3-b982-00ce28f07e2b
-- title:
--   Teich Pair: exists sep
-- statement:
--   The Teich Pair construction uses the exists sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EqZeroOfGe.lean#L15-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EqZeroOfGe.lean#L15-L70

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

theorem GlobalTheory.TeichPair.exists_sep {k O : Type} [CommRing k] [IsDomain k] [CommRing O] {d : ℕ} [NeZero d] {l : ℕ} (hl : 2 ≤ l)
    (f : ZMod d → O →+* k) (hf : ∀ a x, f (a + 1) x = f a x ^ l)
    (hsep : ∀ a a', a ≠ a' → ∃ x, f a x ≠ f a' x) :
    ∃ x, (∀ a, f a x ≠ 0) ∧ Function.Injective fun a => f a x := by sorry
