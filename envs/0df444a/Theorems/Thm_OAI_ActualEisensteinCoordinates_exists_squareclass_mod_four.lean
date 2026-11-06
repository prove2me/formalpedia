-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCoordinates_exists_squareclass_mod_four
-- name    : OAI.ActualEisensteinCoordinates.exists_squareclass_mod_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:33:54.934206+00:00
-- url     : https://prove2.me/theorems/cc4223a7-5c92-4d84-8799-8cc413c48568
-- title:
--   Actual Eisenstein Coordinates: exists squareclass mod four
-- statement:
--   The Actual Eisenstein Coordinates construction uses the exists squareclass mod four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L588-L597
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L588-L597

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

theorem OAI.ActualEisensteinCoordinates.exists_squareclass_mod_four (x : O)
    (hx : EisensteinEPrimaryPhase.odd (residue x)) :
    ∃ (e f : EisensteinEPrimaryPhase.Bit) (u z : O),
      x - lift (EisensteinEPrimaryPhase.rep e f) * u ^ 2 = 4 * z := by sorry
