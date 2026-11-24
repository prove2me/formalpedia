-- Prove2me | Theorems.Thm_MeasureTheory_split_preimage_cylinderOn
-- name    : MeasureTheory.split_preimage_cylinderOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:26:19.990249+00:00
-- url     : https://prove2.me/theorems/22ccc260-05c0-4bfe-afd7-2719204a4a9a
-- title:
--   Measure Theory: split preimage cylinder On
-- statement:
--   The Measure Theory construction uses the split preimage cylinder On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Uniformity.lean#L262-L265
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Uniformity.lean#L262-L265

module
public import Definitions.Def_AddUN_InitialCylinder
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Definitions.Def_AddUN_Uniformity
set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open MeasureTheory
variable (μ : Measure (ℕ → Bool)) [IsFiniteMeasure μ] [NullSingletonClass μ]

theorem MeasureTheory.split_preimage_cylinderOn (n : ℕ) (v : ℕ → Bool) :
    split μ ⁻¹' cylinderOn (Finset.range n) v = cell μ (revPrefix v n) := by sorry
