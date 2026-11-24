-- Prove2me | Theorems.Thm_IdealInvariant_exists_cofinal_mk_eq_cof
-- name    : IdealInvariant.exists_cofinal_mk_eq_cof
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:20:26.159966+00:00
-- url     : https://prove2.me/theorems/cb9aec43-0bb1-4e6c-9316-3db529f21447
-- title:
--   Ideal Invariant: exists cofinal mk eq cof
-- statement:
--   The cofinality is attained.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/IdealInvariant.lean#L81-L87
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/IdealInvariant.lean#L81-L87

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

theorem IdealInvariant.exists_cofinal_mk_eq_cof (I : Set (Set X)) :
    ∃ 𝒜 ⊆ I, (∀ A ∈ I, ∃ B ∈ 𝒜, A ⊆ B) ∧ #𝒜 = cof I := by sorry
