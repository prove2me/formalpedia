-- Prove2me | Theorems.Thm_MeasureTheory_map_split
-- name    : MeasureTheory.map_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:31:42.772919+00:00
-- url     : https://prove2.me/theorems/dea4c208-d80a-4d52-83d2-2f085b3343d0
-- title:
--   Measure Theory: map split
-- statement:
--   The map `split μ` sends `μ` to `μ univ` times the coin-tossing measure.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Uniformity.lean#L275-L279
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Uniformity.lean#L275-L279

module
public import Definitions.Def_AddUN_InitialCylinder
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Definitions.Def_AddUN_Uniformity
public import Theorems.Thm_MeasureTheory_Determined_univ

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open MeasureTheory
variable (μ : Measure (ℕ → Bool)) [IsFiniteMeasure μ] [NullSingletonClass μ]

theorem MeasureTheory.map_split : μ.map (split μ) = μ univ • cantorMeasure := by sorry
