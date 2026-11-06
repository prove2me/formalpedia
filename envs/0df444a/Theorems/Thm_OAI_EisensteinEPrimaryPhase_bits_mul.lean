-- Prove2me | Theorems.Thm_OAI_EisensteinEPrimaryPhase_bits_mul
-- name    : OAI.EisensteinEPrimaryPhase.bits_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:21:47.049072+00:00
-- url     : https://prove2.me/theorems/51b53b5c-3776-4c97-b4be-879a63603edc
-- title:
--   Eisenstein EPrimary Phase: bits mul
-- statement:
--   The Eisenstein EPrimary Phase construction uses the bits mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L417-L419
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L417-L419

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

theorem OAI.EisensteinEPrimaryPhase.bits_mul (x y : Coord) (hx : odd x) (hy : odd y) :
    bits (mul x y) = bits x + bits y := by sorry
