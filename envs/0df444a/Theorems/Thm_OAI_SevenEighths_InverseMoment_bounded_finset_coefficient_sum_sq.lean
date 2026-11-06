-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_bounded_finset_coefficient_sum_sq
-- name    : OAI.SevenEighths.InverseMoment.bounded_finset_coefficient_sum_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:25:48.325704+00:00
-- url     : https://prove2.me/theorems/6521c44e-5db7-4c4e-b88b-6f92a65806d2
-- title:
--   Inverse Moment: bounded finset coefficient sum sq
-- statement:
--   The Inverse Moment construction uses the bounded finset coefficient sum sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/SieveComposition.lean#L11-L18
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/SieveComposition.lean#L11-L18

import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Fibers
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_SieveComposition
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators
noncomputable section

theorem OAI.SevenEighths.InverseMoment.bounded_finset_coefficient_sum_sq {C : Type*} (s : Finset C)
    (b f : C → ℂ) (hb : ∀ c ∈ s, ‖b c‖ ≤ 1) :
    ‖∑ c ∈ s, b c * f c‖ ^ 2 ≤ (s.card : ℝ) * ∑ c ∈ s, ‖f c‖ ^ 2 := by sorry
