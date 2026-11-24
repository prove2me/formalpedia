-- Prove2me | Theorems.Thm_MeasureTheory_IsUniversallyNull_of_injOn_restrict
-- name    : MeasureTheory.IsUniversallyNull.of_injOn_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:37:17.637591+00:00
-- url     : https://prove2.me/theorems/b3554c9e-f23c-4155-af9a-959f39f4fb4a
-- title:
--   Is Universally Null: of inj On restrict
-- statement:
--   **Lemma 3, partial maps.** Let `Δ` be measurable and `φ` measurable on `Δ`. Let `A ⊆ Δ` be
--   such that `φ` is injective on `A` and maps `A` into a universally null set `P`. Then `A` is
--   universally null.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Transfer.lean#L70-L80
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Transfer.lean#L70-L80

module
public import Definitions.Def_AddUN_UniversallyNull
public import Definitions.Def_AddUN_Transfer
set_option autoImplicit false
@[expose] public section
public section
open Set
open MeasureTheory
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSingletonClass Y]

theorem MeasureTheory.IsUniversallyNull.of_injOn_restrict {P : Set Y} (hP : IsUniversallyNull P) {Δ : Set X}
    (hΔ : MeasurableSet Δ) {φ : X → Y} (hφ : Measurable (Δ.domRestrict φ)) {A : Set X}
    (hA : A ⊆ Δ) (hinj : InjOn φ A) (himg : φ '' A ⊆ P) : IsUniversallyNull A := by sorry
