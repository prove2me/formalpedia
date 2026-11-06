-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCoordinates_ePrimary_squareclass_actual
-- name    : OAI.ActualEisensteinCoordinates.ePrimary_squareclass_actual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:33:57.33666+00:00
-- url     : https://prove2.me/theorems/29063448-e8bb-4cf4-8a32-0dba82743859
-- title:
--   Actual Eisenstein Coordinates: e Primary squareclass actual
-- statement:
--   The Actual Eisenstein Coordinates construction uses the e Primary squareclass actual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L599-L605
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L599-L605

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

theorem OAI.ActualEisensteinCoordinates.ePrimary_squareclass_actual
    (e f : EisensteinEPrimaryPhase.Bit) (u : O)
    (hu : EisensteinEPrimaryPhase.odd (residue u)) :
    EisensteinEPrimaryPhase.ePrimary
      (residue (lift (EisensteinEPrimaryPhase.rep e f) * u ^ 2)) ↔ e = 0 := by sorry
