-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCoordinates_odd_residue_iff_not_two_dvd
-- name    : OAI.ActualEisensteinCoordinates.odd_residue_iff_not_two_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:22:01.064014+00:00
-- url     : https://prove2.me/theorems/eda517d7-0493-48a3-855f-05c99b957a0a
-- title:
--   Actual Eisenstein Coordinates: odd residue iff not two dvd
-- statement:
--   The Actual Eisenstein Coordinates construction uses the odd residue iff not two dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L632-L654
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L632-L654

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

theorem OAI.ActualEisensteinCoordinates.odd_residue_iff_not_two_dvd (x : O) :
    EisensteinEPrimaryPhase.odd (residue x) ↔ ¬ (2 : O) ∣ x := by sorry
