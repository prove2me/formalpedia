-- Prove2me | Theorems.Thm_MeasureTheory_flip_flip
-- name    : MeasureTheory.flip_flip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:22:04.163429+00:00
-- url     : https://prove2.me/theorems/1af35dd2-2093-4384-8b44-08c2f813ebf6
-- title:
--   Measure Theory: flip flip
-- statement:
--   The Measure Theory construction uses the flip flip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L44-L46
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L44-L46

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

theorem MeasureTheory.flip_flip (i : ℕ) (w : ℕ → Bool) : flip i (flip i w) = w := by sorry
