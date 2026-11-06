-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_primeMark_indexed_assignments
-- name    : OAI.SevenEighths.InverseMoment.primeMark_indexed_assignments
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T23:02:09.096051+00:00
-- url     : https://prove2.me/theorems/14c41c70-e803-4df6-97cf-02bed68025b7
-- title:
--   Inverse Moment: prime Mark indexed assignments
-- statement:
--   The Inverse Moment construction uses the prime Mark indexed assignments property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/SlotAssignments.lean#L46-L53
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/SlotAssignments.lean#L46-L53

import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Marks
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_SlotAssignments
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

theorem OAI.SevenEighths.InverseMoment.primeMark_indexed_assignments (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) :
    primeMark I L a A =
      ∑ r ∈ (I.pi (fun i => L i ∩ A)).image (indexedSlotAssignment I),
        slotAssignmentWeight I a (fun i hi => r (I.equivFin ⟨i,hi⟩)) := by sorry
