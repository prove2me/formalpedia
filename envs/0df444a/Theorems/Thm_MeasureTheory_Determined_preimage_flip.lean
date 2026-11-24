-- Prove2me | Theorems.Thm_MeasureTheory_Determined_preimage_flip
-- name    : MeasureTheory.Determined.preimage_flip
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:29:18.568368+00:00
-- url     : https://prove2.me/theorems/e87dc140-3f03-411f-a230-3c6d1e3ec060
-- title:
--   Determined: preimage flip
-- statement:
--   An event that does not depend on the coordinate `i` is invariant under the flip at `i`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L114-L116
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L114-L116

module
public import Definitions.Def_AddUN_UniversallyNull
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.ClopenBox
public import Definitions.Def_AddUN_CantorMeasure
set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace
open scoped ENNReal
open MeasureTheory
open MeasureTheory.Determined
variable {s t : Set ℕ} {E F : Set (ℕ → Bool)}

theorem MeasureTheory.Determined.preimage_flip {i : ℕ} (hE : Determined s E) (hi : i ∉ s) : flip i ⁻¹' E = E := by sorry
