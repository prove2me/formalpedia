-- Prove2me | Theorems.Thm_IdealInvariant_sUnion_mem_of_lt_add
-- name    : IdealInvariant.sUnion_mem_of_lt_add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:21:37.283075+00:00
-- url     : https://prove2.me/theorems/fcf90043-f854-482e-a79b-765d6dd0ce02
-- title:
--   Ideal Invariant: s Union mem of lt add
-- statement:
--   A subfamily of `I` of size less than `add I` has its union in `I`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/IdealInvariant.lean#L66-L67
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/IdealInvariant.lean#L66-L67

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

theorem IdealInvariant.sUnion_mem_of_lt_add (h𝒜 : 𝒜 ⊆ I) (h : #𝒜 < add I) : ⋃₀ 𝒜 ∈ I := by sorry
