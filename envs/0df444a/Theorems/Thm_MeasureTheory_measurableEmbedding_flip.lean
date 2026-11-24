-- Prove2me | Theorems.Thm_MeasureTheory_measurableEmbedding_flip
-- name    : MeasureTheory.measurableEmbedding_flip
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:28:42.916559+00:00
-- url     : https://prove2.me/theorems/436bb08e-5b9f-44cf-9445-dc62fa781b0f
-- title:
--   Measure Theory: measurable Embedding flip
-- statement:
--   The Measure Theory construction uses the measurable Embedding flip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L76-L83
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L76-L83

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

theorem MeasureTheory.measurableEmbedding_flip (i : ℕ) : MeasurableEmbedding (flip i) := by sorry
