-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCoordinates_rayPhase_mul_right
-- name    : OAI.ActualEisensteinCoordinates.rayPhase_mul_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:34:41.0762+00:00
-- url     : https://prove2.me/theorems/9e67be44-b35a-48ed-bded-e4e28f56265d
-- title:
--   Actual Eisenstein Coordinates: ray Phase mul right
-- statement:
--   The Actual Eisenstein Coordinates construction uses the ray Phase mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L696-L701
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L696-L701

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

theorem OAI.ActualEisensteinCoordinates.rayPhase_mul_right (x y z : O)
    (hy : ¬ (2 : O) ∣ y) (hz : ¬ (2 : O) ∣ z) :
    rayPhase x (y*z) = rayPhase x y * rayPhase x z := by sorry
