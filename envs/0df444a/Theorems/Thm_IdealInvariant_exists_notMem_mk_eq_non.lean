-- Prove2me | Theorems.Thm_IdealInvariant_exists_notMem_mk_eq_non
-- name    : IdealInvariant.exists_notMem_mk_eq_non
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:20:24.965662+00:00
-- url     : https://prove2.me/theorems/55b59b56-f0d8-4d5e-ac9e-0edc98e3947e
-- title:
--   Ideal Invariant: exists not Mem mk eq non
-- statement:
--   The uniformity is attained when some set is not in `I`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/IdealInvariant.lean#L74-L78
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/IdealInvariant.lean#L74-L78

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

theorem IdealInvariant.exists_notMem_mk_eq_non (hI : ∃ A, A ∉ I) : ∃ A, A ∉ I ∧ #A = non I := by sorry
