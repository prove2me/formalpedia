-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCoordinates_norm_squareclass_actual
-- name    : OAI.ActualEisensteinCoordinates.norm_squareclass_actual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:34:34.719952+00:00
-- url     : https://prove2.me/theorems/5e09f9b3-5c0d-47a6-ba6c-d8257d9f5f7b
-- title:
--   Actual Eisenstein Coordinates: norm squareclass actual
-- statement:
--   The Actual Eisenstein Coordinates construction uses the norm squareclass actual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L607-L614
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L607-L614

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

theorem OAI.ActualEisensteinCoordinates.norm_squareclass_actual
    (e f : EisensteinEPrimaryPhase.Bit) (u : O)
    (hu : EisensteinEPrimaryPhase.odd (residue u)) :
    EisensteinEPrimaryPhase.norm
      (residue (lift (EisensteinEPrimaryPhase.rep e f) * u ^ 2)) =
      (if f = 0 then 1 else 3) := by sorry
