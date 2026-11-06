-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_indexedSlotAssignment_support
-- name    : OAI.SevenEighths.InverseMoment.indexedSlotAssignment_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T23:02:10.011481+00:00
-- url     : https://prove2.me/theorems/1881e1cb-6944-4b44-a06a-d39874386499
-- title:
--   Inverse Moment: indexed Slot Assignment support
-- statement:
--   The Inverse Moment construction uses the indexed Slot Assignment support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/SlotAssignments.lean#L40-L44
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/SlotAssignments.lean#L40-L44

import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Marks
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_SlotAssignments
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

theorem OAI.SevenEighths.InverseMoment.indexedSlotAssignment_support (I : Finset σ) (L : σ → Finset ι)
    (A : Finset ι) (q : ∀ i ∈ I, ι) (hq : q ∈ I.pi (fun i => L i ∩ A))
    (j : Fin I.card) :
    indexedSlotAssignment I q j ∈ L ((I.equivFin).symm j).val ∩ A := by sorry
