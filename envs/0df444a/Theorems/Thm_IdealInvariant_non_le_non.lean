-- Prove2me | Theorems.Thm_IdealInvariant_non_le_non
-- name    : IdealInvariant.non_le_non
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:27:40.220251+00:00
-- url     : https://prove2.me/theorems/ec845f9a-0fd7-47ff-98f4-e22e34ce4d86
-- title:
--   Ideal Invariant: non le non
-- statement:
--   The uniformity is monotone: a smaller family has a smaller uniformity, provided the larger
--   family does not contain every set.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/IdealInvariant.lean#L127-L129
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/IdealInvariant.lean#L127-L129

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

theorem IdealInvariant.non_le_non {J : Set (Set X)} (hIJ : I ⊆ J) (hJ : ∃ A, A ∉ J) : non I ≤ non J := by sorry
