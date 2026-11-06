-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_primeMark_supported_assignments
-- name    : OAI.SevenEighths.InverseMoment.primeMark_supported_assignments
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:27:47.708932+00:00
-- url     : https://prove2.me/theorems/7d68d2b1-7431-4c35-8685-0703751c072f
-- title:
--   Inverse Moment: prime Mark supported assignments
-- statement:
--   The Inverse Moment construction uses the prime Mark supported assignments property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/SlotAssignments.lean#L14-L18
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/SlotAssignments.lean#L14-L18

import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Marks
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_SlotAssignments
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

theorem OAI.SevenEighths.InverseMoment.primeMark_supported_assignments (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) :
    primeMark I L a A = ∑ q ∈ I.pi (fun i => L i ∩ A), slotAssignmentWeight I a q := by sorry
