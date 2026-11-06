-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCoordinates_eval_mul
-- name    : OAI.ActualEisensteinCoordinates.eval_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:21:57.658659+00:00
-- url     : https://prove2.me/theorems/cc5e0150-e69d-479a-8ff3-27d8afddb508
-- title:
--   Actual Eisenstein Coordinates: eval mul
-- statement:
--   The Actual Eisenstein Coordinates construction uses the eval mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L517-L527
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L517-L527

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
open OAI.ActualEisensteinCoordinates

theorem OAI.ActualEisensteinCoordinates.eval_mul (a b c d : ℤ) :
    eval a b * eval c d = eval (a*c-b*d) (a*d+b*c-b*d) := by sorry
