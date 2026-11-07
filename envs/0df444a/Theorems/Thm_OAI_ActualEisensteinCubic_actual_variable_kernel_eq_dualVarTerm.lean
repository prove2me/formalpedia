-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_actual_variable_kernel_eq_dualVarTerm
-- name    : OAI.ActualEisensteinCubic.actual_variable_kernel_eq_dualVarTerm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:43:39.936962+00:00
-- url     : https://prove2.me/theorems/3ef907af-fabb-475e-9074-251b83b00325
-- title:
--   Actual Eisenstein Cubic: actual variable kernel eq dual Var Term
-- statement:
--   The Actual Eisenstein Cubic construction uses the actual variable kernel eq dual Var Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ThetaLocalRows.lean#L103-L118
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ThetaLocalRows.lean#L103-L118

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_AbelPhaseLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows
set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
open EisensteinEmbedding ConcreteTraceCRT Complex
open scoped Topology
open Filter

theorem OAI.ActualEisensteinCubic.actual_variable_kernel_eq_dualVarTerm
    (a b : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) (hη : 0 < η) (z : ℤ × ℤ) :
    actualVariableDualKernel a b η (dualFrequencyEquiv z) =
      OscSpecial.dualVarTerm η (a : ℝ) (b : ℝ) z := by sorry
