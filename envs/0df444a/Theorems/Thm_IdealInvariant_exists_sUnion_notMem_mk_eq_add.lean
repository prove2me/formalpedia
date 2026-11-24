-- Prove2me | Theorems.Thm_IdealInvariant_exists_sUnion_notMem_mk_eq_add
-- name    : IdealInvariant.exists_sUnion_notMem_mk_eq_add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:30:00.718509+00:00
-- url     : https://prove2.me/theorems/5e700eaa-fb8e-4e59-984c-37b73d1b1186
-- title:
--   Ideal Invariant: exists s Union not Mem mk eq add
-- statement:
--   The additivity is attained when some subfamily of `I` has its union outside `I`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Localisation.lean#L36-L42
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Localisation.lean#L36-L42

module
public import Definitions.Def_AddUN_CantorMeasure
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Topology.Separation.Profinite
public import Definitions.Def_AddUN_Localisation
set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open IdealInvariant
universe u
variable {X : Type u} {I : Set (Set X)}

theorem IdealInvariant.exists_sUnion_notMem_mk_eq_add (hI : ∃ 𝒜 ⊆ I, ⋃₀ 𝒜 ∉ I) :
    ∃ 𝒜 ⊆ I, ⋃₀ 𝒜 ∉ I ∧ #𝒜 = add I := by sorry
