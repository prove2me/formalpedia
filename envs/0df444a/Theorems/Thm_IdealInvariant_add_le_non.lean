-- Prove2me | Theorems.Thm_IdealInvariant_add_le_non
-- name    : IdealInvariant.add_le_non
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:20:28.843429+00:00
-- url     : https://prove2.me/theorems/96ce05d1-44fb-410b-b4a2-14a17c8ee3bc
-- title:
--   Ideal Invariant: add le non
-- statement:
--   If `I` contains every singleton and some set is not in `I`, then `add I ≤ non I`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/IdealInvariant.lean#L101-L109
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/IdealInvariant.lean#L101-L109

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

theorem IdealInvariant.add_le_non (hsing : ∀ x, {x} ∈ I) (hI : ∃ A, A ∉ I) : add I ≤ non I := by sorry
