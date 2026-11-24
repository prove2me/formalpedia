-- Prove2me | Theorems.Thm_MeasureTheory_IsUniversallyNull_of_injOn
-- name    : MeasureTheory.IsUniversallyNull.of_injOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:22:19.191825+00:00
-- url     : https://prove2.me/theorems/2752346a-288a-48ae-94a5-c231c8e2e0fa
-- title:
--   Is Universally Null: of inj On
-- statement:
--   **Lemma 3.** Let `φ` be measurable, injective on `A`, and map `A` into a universally null
--   set `P`. Then `A` is universally null.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Transfer.lean#L29-L65
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Transfer.lean#L29-L65

module
public import Definitions.Def_AddUN_UniversallyNull
public import Definitions.Def_AddUN_Transfer
set_option autoImplicit false
@[expose] public section
public section
open Set
open MeasureTheory
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSingletonClass Y]

theorem MeasureTheory.IsUniversallyNull.of_injOn {P : Set Y} (hP : IsUniversallyNull P) {φ : X → Y}
    (hφ : Measurable φ) {A : Set X} (hinj : InjOn φ A) (himg : φ '' A ⊆ P) :
    IsUniversallyNull A := by sorry
