-- Prove2me | Theorems.Thm_OAI_SevenEighths_Supremum_exists_gt_supremum_sub_of_insert
-- name    : OAI.SevenEighths.Supremum.exists_gt_supremum_sub_of_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:15:49.70299+00:00
-- url     : https://prove2.me/theorems/17a35b2e-ad97-47c8-a137-ac82e2bb721d
-- title:
--   Supremum: exists gt supremum sub of insert
-- statement:
--   The Supremum construction uses the exists gt supremum sub of insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Supremum.lean#L57-L66
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Supremum.lean#L57-L66

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_OAI_NumberTheory_DirichletL_Supremum
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Supremum
noncomputable section

theorem OAI.SevenEighths.Supremum.exists_gt_supremum_sub_of_insert {S : Set ℝ} {a ε : ℝ}
    (hbounded : BddAbove (insert a S)) (hε : 0 < ε)
    (ha : a ≤ sSup (insert a S) - ε) :
    ∃ x ∈ S, sSup (insert a S) - ε < x := by sorry
