-- Prove2me | Theorems.Thm_OAI_EisensteinEPrimaryPhase_squareclass_bits_unique
-- name    : OAI.EisensteinEPrimaryPhase.squareclass_bits_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:33:37.479667+00:00
-- url     : https://prove2.me/theorems/a45c379a-1dc7-452a-b69b-42d18807866e
-- title:
--   Eisenstein EPrimary Phase: squareclass bits unique
-- statement:
--   The Eisenstein EPrimary Phase construction uses the squareclass bits unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L392-L396
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L392-L396

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

theorem OAI.EisensteinEPrimaryPhase.squareclass_bits_unique (e f e' f' : Bit) (u v : Coord)
    (hu : odd u) (hv : odd v)
    (h : mul (rep e f) (mul u u) = mul (rep e' f') (mul v v)) :
    e = e' ∧ f = f' := by sorry
