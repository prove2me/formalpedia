-- Prove2me | Theorems.Thm_OAI_SevenEighths_Supremum_exists_gt_supremum_sub
-- name    : OAI.SevenEighths.Supremum.exists_gt_supremum_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:43:00.07621+00:00
-- url     : https://prove2.me/theorems/cdf099af-e701-4ecf-b09d-14acdefe6532
-- title:
--   Supremum: exists gt supremum sub
-- statement:
--   The Supremum construction uses the exists gt supremum sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Supremum.lean#L45-L49
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Supremum.lean#L45-L49

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_OAI_NumberTheory_DirichletL_Supremum
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Supremum
noncomputable section

theorem OAI.SevenEighths.Supremum.exists_gt_supremum_sub {S : Set ℝ} (hne : S.Nonempty)
    (hbounded : BddAbove S) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ S, sSup S - ε < x := by sorry
