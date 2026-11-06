-- Prove2me | Theorems.Thm_OAI_EisensteinEPrimaryPhase_odd_mul
-- name    : OAI.EisensteinEPrimaryPhase.odd_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:33:50.842203+00:00
-- url     : https://prove2.me/theorems/edc459b7-fcdc-4fd5-bf70-175d28026b09
-- title:
--   Eisenstein EPrimary Phase: odd mul
-- statement:
--   The Eisenstein EPrimary Phase construction uses the odd mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L414-L415
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L414-L415

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
open OAI.EisensteinEPrimaryPhase

theorem OAI.EisensteinEPrimaryPhase.odd_mul (x y : Coord) (hx : odd x) (hy : odd y) : odd (mul x y) := by sorry
