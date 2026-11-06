-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_eis_gaussian_summable
-- name    : OAI.ActualEisensteinCubic.eis_gaussian_summable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:46:05.802527+00:00
-- url     : https://prove2.me/theorems/f4d3d191-13f7-457a-bc46-ac9ec810cf68
-- title:
--   Actual Eisenstein Cubic: eis gaussian summable
-- statement:
--   The Actual Eisenstein Cubic construction uses the eis gaussian summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/GaussianFiberMass.lean#L330-L355
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/GaussianFiberMass.lean#L330-L355

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
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
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex

theorem OAI.ActualEisensteinCubic.eis_gaussian_summable {η : ℝ} (hη : 0 < η) :
    Summable (fun z : O => Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
      (‖eisEmbedding z‖ ^ 2 : ℂ))) := by sorry
