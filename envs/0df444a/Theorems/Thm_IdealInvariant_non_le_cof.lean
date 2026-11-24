-- Prove2me | Theorems.Thm_IdealInvariant_non_le_cof
-- name    : IdealInvariant.non_le_cof
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:20:28.869436+00:00
-- url     : https://prove2.me/theorems/b50328c6-84a4-40c4-abb9-7ba2c3630659
-- title:
--   Ideal Invariant: non le cof
-- statement:
--   If the whole space is not in `I`, then `non I ≤ cof I`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/IdealInvariant.lean#L112-L123
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/IdealInvariant.lean#L112-L123

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

theorem IdealInvariant.non_le_cof (huniv : univ ∉ I) : non I ≤ cof I := by sorry
