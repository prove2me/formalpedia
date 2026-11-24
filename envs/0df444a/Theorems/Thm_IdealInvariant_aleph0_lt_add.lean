-- Prove2me | Theorems.Thm_IdealInvariant_aleph0_lt_add
-- name    : IdealInvariant.aleph0_lt_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:20:27.804994+00:00
-- url     : https://prove2.me/theorems/82bbb15b-ab14-4db1-b9e3-a045b7127667
-- title:
--   Ideal Invariant: aleph0 lt add
-- statement:
--   If `I` is closed under countable unions and some subfamily of `I` has its union outside `I`,
--   then `add I` is uncountable.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/IdealInvariant.lean#L91-L98
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/IdealInvariant.lean#L91-L98

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

theorem IdealInvariant.aleph0_lt_add (hσ : ∀ 𝒜 ⊆ I, 𝒜.Countable → ⋃₀ 𝒜 ∈ I) (hI : ∃ 𝒜 ⊆ I, ⋃₀ 𝒜 ∉ I) :
    ℵ₀ < add I := by sorry
