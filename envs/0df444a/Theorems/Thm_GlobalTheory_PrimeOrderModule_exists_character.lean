-- Prove2me | Theorems.Thm_GlobalTheory_PrimeOrderModule_exists_character
-- name    : GlobalTheory.PrimeOrderModule.exists_character
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:19:04.057069+00:00
-- url     : https://prove2.me/theorems/9c17fdf3-ed3c-5f59-aa6e-a833f3c865f4
-- title:
--   Prime Order Module: exists character
-- statement:
--   The Prime Order Module construction uses the exists character property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ImportsExtra.lean#L5-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ImportsExtra.lean#L5-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsExtra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PrimeOrderModule

theorem GlobalTheory.PrimeOrderModule.exists_character (S M : Type) [CommRing S] [AddCommGroup M] [Module S M] (T : ℕ)
    (hT : T.Prime) (hM : Nat.card M = T) :
    ∃ χ : S →+* ZMod T, ∀ (a : S) (m : M), χ a = 0 → a • m = 0 := by sorry
