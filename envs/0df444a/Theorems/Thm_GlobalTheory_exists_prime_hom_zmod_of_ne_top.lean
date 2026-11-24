-- Prove2me | Theorems.Thm_GlobalTheory_exists_prime_hom_zmod_of_ne_top
-- name    : GlobalTheory.exists_prime_hom_zmod_of_ne_top
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:36:37.801838+00:00
-- url     : https://prove2.me/theorems/36941fce-0994-4ca2-898f-42633741756d
-- title:
--   Global Theory: exists prime hom zmod of ne top
-- statement:
--   The Global Theory construction uses the exists prime hom zmod of ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsPrimeHomZmodOfNeTop.lean#L5-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsPrimeHomZmodOfNeTop.lean#L5-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsPrimeHomZmodOfNeTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_prime_hom_zmod_of_ne_top (X : Type) [AddCommGroup X] [Module.Finite ℤ X]
    (Λ : AddSubgroup X) (h : Λ ≠ ⊤) :
    ∃ l : ℕ, l.Prime ∧ ∃ f : X →+ ZMod l, f ≠ 0 ∧ ∀ x ∈ Λ, f x = 0 := by sorry
