-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_eval_norm_sq
-- name    : OAI.ActualEisensteinCubic.eisEmbedding_eval_norm_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:44:29.421+00:00
-- url     : https://prove2.me/theorems/f3019e1e-d3a9-4b5c-9f26-767186b4c54f
-- title:
--   Actual Eisenstein Cubic: eis Embedding eval norm sq
-- statement:
--   The Actual Eisenstein Cubic construction uses the eis Embedding eval norm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/BinaryGaussian.lean#L428-L443
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/BinaryGaussian.lean#L428-L443

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
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
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex

theorem OAI.ActualEisensteinCubic.eisEmbedding_eval_norm_sq (x y : ℤ) :
    ‖eisEmbedding (ActualEisensteinCoordinates.eval x y)‖ ^ 2 =
      (x*x-x*y+y*y : ℤ) := by sorry
