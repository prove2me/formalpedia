-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_indexedSlotAssignment_injective
-- name    : OAI.SevenEighths.InverseMoment.indexedSlotAssignment_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:27:49.052209+00:00
-- url     : https://prove2.me/theorems/df7f4032-dd5b-4ed9-8fae-1d9651544065
-- title:
--   Inverse Moment: indexed Slot Assignment injective
-- statement:
--   The Inverse Moment construction uses the indexed Slot Assignment injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/SlotAssignments.lean#L33-L38
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/SlotAssignments.lean#L33-L38

import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Marks
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_SlotAssignments
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]
omit [DecidableEq σ] [DecidableEq ι]

theorem OAI.SevenEighths.InverseMoment.indexedSlotAssignment_injective (I : Finset σ) :
    Function.Injective (indexedSlotAssignment (ι:=ι) I) := by sorry
