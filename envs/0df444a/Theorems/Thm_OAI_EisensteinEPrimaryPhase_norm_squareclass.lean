-- Prove2me | Theorems.Thm_OAI_EisensteinEPrimaryPhase_norm_squareclass
-- name    : OAI.EisensteinEPrimaryPhase.norm_squareclass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:21:46.705404+00:00
-- url     : https://prove2.me/theorems/0e2cdac6-8019-41b5-b3ff-aa1458534e2b
-- title:
--   Eisenstein EPrimary Phase: norm squareclass
-- statement:
--   The Eisenstein EPrimary Phase construction uses the norm squareclass property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L402-L404
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L402-L404

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

theorem OAI.EisensteinEPrimaryPhase.norm_squareclass (e f : Bit) (u : Coord) (hu : odd u) :
    norm (mul (rep e f) (mul u u)) = (if f = 0 then 1 else 3) := by sorry
