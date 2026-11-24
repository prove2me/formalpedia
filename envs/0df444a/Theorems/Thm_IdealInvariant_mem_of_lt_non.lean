-- Prove2me | Theorems.Thm_IdealInvariant_mem_of_lt_non
-- name    : IdealInvariant.mem_of_lt_non
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:20:28.064234+00:00
-- url     : https://prove2.me/theorems/0bf80b9b-db88-496f-8738-deb47fdeb701
-- title:
--   Ideal Invariant: mem of lt non
-- statement:
--   A set of size less than `non I` is in `I`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/IdealInvariant.lean#L70-L71
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/IdealInvariant.lean#L70-L71

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

theorem IdealInvariant.mem_of_lt_non (h : #A < non I) : A ∈ I := by sorry
