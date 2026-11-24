-- Prove2me | Theorems.Thm_IdealInvariant_add_le
-- name    : IdealInvariant.add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:20:19.498842+00:00
-- url     : https://prove2.me/theorems/899c2377-1631-4b12-899a-14d19cecded4
-- title:
--   Ideal Invariant: add le
-- statement:
--   The Ideal Invariant construction uses the add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/IdealInvariant.lean#L52-L53
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/IdealInvariant.lean#L52-L53

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

theorem IdealInvariant.add_le (h𝒜 : 𝒜 ⊆ I) (hU : ⋃₀ 𝒜 ∉ I) : add I ≤ #𝒜 := by sorry
