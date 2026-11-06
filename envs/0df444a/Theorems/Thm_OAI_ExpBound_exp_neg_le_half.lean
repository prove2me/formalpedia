-- Prove2me | Theorems.Thm_OAI_ExpBound_exp_neg_le_half
-- name    : OAI.ExpBound.exp_neg_le_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:51:17.630674+00:00
-- url     : https://prove2.me/theorems/830862f1-53ea-4c4c-8057-58ee75b0560b
-- title:
--   Exp Bound: exp neg le half
-- statement:
--   The Exp Bound construction uses the exp neg le half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/ExponentialSmoothing.lean#L324-L332
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/ExponentialSmoothing.lean#L324-L332

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ExpBound

theorem OAI.ExpBound.exp_neg_le_half {t : ℝ} (ht : 1 ≤ t) :
    Real.exp (-t) ≤ (1 : ℝ) / 2 := by sorry
