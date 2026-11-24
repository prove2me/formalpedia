-- Prove2me | Theorems.Thm_MeasureTheory_cantorMeasure_inter_coord
-- name    : MeasureTheory.cantorMeasure_inter_coord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:29:25.255527+00:00
-- url     : https://prove2.me/theorems/9b909780-de59-45da-b623-27373c54e277
-- title:
--   Measure Theory: cantor Measure inter coord
-- statement:
--   An event that is invariant under the flip at `i` is split into two halves of equal measure
--   by the coordinate `i`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L152-L169
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L152-L169

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

theorem MeasureTheory.cantorMeasure_inter_coord {E : Set (ℕ → Bool)} {i : ℕ} (hflip : flip i ⁻¹' E = E)
    (b : Bool) : cantorMeasure (E ∩ {w | w i = b}) = cantorMeasure E / 2 := by sorry
