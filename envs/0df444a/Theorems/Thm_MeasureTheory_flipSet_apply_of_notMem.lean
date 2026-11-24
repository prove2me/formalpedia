-- Prove2me | Theorems.Thm_MeasureTheory_flipSet_apply_of_notMem
-- name    : MeasureTheory.flipSet_apply_of_notMem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:26:40.819168+00:00
-- url     : https://prove2.me/theorems/721b1454-477e-4f98-aa1b-f3fc4252800a
-- title:
--   Measure Theory: flip Set apply of not Mem
-- statement:
--   The Measure Theory construction uses the flip Set apply of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/ZeroOne.lean#L35-L37
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/ZeroOne.lean#L35-L37

module
public import Definitions.Def_AddUN_InitialCylinder
public import Definitions.Def_AddUN_ZeroOne
set_option autoImplicit false
@[expose] public section
public section
open Set
open MeasureTheory

theorem MeasureTheory.flipSet_apply_of_notMem {s : Finset ℕ} {j : ℕ} (h : j ∉ s) (w : ℕ → Bool) :
    flipSet s w j = w j := by sorry
