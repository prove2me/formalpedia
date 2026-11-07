-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_actual_fixed_kernel_eq_dualFixedTerm_point
-- name    : OAI.ActualEisensteinCubic.actual_fixed_kernel_eq_dualFixedTerm_point
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:43:42.09455+00:00
-- url     : https://prove2.me/theorems/ba9c58d4-b79b-46a9-acdb-18f211e6e0e9
-- title:
--   Actual Eisenstein Cubic: actual fixed kernel eq dual Fixed Term point
-- statement:
--   The Actual Eisenstein Cubic construction uses the actual fixed kernel eq dual Fixed Term point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ThetaLocalRows.lean#L120-L125
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ThetaLocalRows.lean#L120-L125

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

theorem OAI.ActualEisensteinCubic.actual_fixed_kernel_eq_dualFixedTerm_point
    (a b : ℤ) (η : ℝ) (z : ℤ × ℤ) :
    actualFixedDualKernel a b η (dualFrequencyEquiv z) =
      OscSpecial.dualFixedTerm η (a : ℝ) (b : ℝ) z := by sorry
