-- Prove2me | Theorems.Thm_IdealInvariant_non_le
-- name    : IdealInvariant.non_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:20:26.141799+00:00
-- url     : https://prove2.me/theorems/2ec347be-3809-4415-a67b-17d2fa5cf153
-- title:
--   Ideal Invariant: non le
-- statement:
--   The Ideal Invariant construction uses the non le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/IdealInvariant.lean#L58-L59
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/IdealInvariant.lean#L58-L59

module
public import Mathlib.SetTheory.Cardinal.Basic
public import Definitions.Def_AddUN_IdealInvariant
set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Set
open IdealInvariant
variable {X : Type u} {I : Set (Set X)} {𝒜 : Set (Set X)} {A : Set X}

theorem IdealInvariant.non_le (hA : A ∉ I) : non I ≤ #A := by sorry
