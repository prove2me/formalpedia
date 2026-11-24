-- Prove2me | Theorems.Thm_MeasureTheory_measure_eq_zero_or_one_of_flipSet_invariant
-- name    : MeasureTheory.measure_eq_zero_or_one_of_flipSet_invariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:32:17.468016+00:00
-- url     : https://prove2.me/theorems/44ebed45-3527-441c-b186-e66fdbefda73
-- title:
--   Measure Theory: measure eq zero or one of flip Set invariant
-- statement:
--   **A zero–one law.** A measurable set that is invariant under every finite flip has measure
--   `0` or `1`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/ZeroOne.lean#L62-L95
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/ZeroOne.lean#L62-L95

module
public import Definitions.Def_AddUN_InitialCylinder
public import Definitions.Def_AddUN_ZeroOne
set_option autoImplicit false
@[expose] public section
public section
open Set
open MeasureTheory

theorem MeasureTheory.measure_eq_zero_or_one_of_flipSet_invariant {E : Set (ℕ → Bool)} (hE : MeasurableSet E)
    (hinv : ∀ t : Finset ℕ, flipSet t ⁻¹' E = E) :
    cantorMeasure E = 0 ∨ cantorMeasure E = 1 := by sorry
