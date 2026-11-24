-- Prove2me | Theorems.Thm_GlobalTheory_ConjIdeal_exists_eq_nsmul_of_forall_addChar
-- name    : GlobalTheory.ConjIdeal.exists_eq_nsmul_of_forall_addChar
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:25:01.605106+00:00
-- url     : https://prove2.me/theorems/7696a3ad-925b-4ddb-9799-7e4a8fcab2ad
-- title:
--   Conj Ideal: exists eq nsmul of forall add Char
-- statement:
--   The Conj Ideal construction uses the exists eq nsmul of forall add Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsEqNsmulOfForallAddChar.lean#L21-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsEqNsmulOfForallAddChar.lean#L21-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsEqNsmulOfForallAddChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.ConjIdeal

theorem GlobalTheory.ConjIdeal.exists_eq_nsmul_of_forall_addChar {X : Type*} [AddCommGroup X] [Module.Free ℤ X] {M : ℕ}
    (hM : M ≠ 0) {C : Type*} [CommMonoid C] {ζ : C} (hζ : IsPrimitiveRoot ζ M) (v : X)
    (h : ∀ t : AddChar X C, (∀ x, t x ^ M = 1) → t v = 1) : ∃ z : X, v = M • z := by sorry
