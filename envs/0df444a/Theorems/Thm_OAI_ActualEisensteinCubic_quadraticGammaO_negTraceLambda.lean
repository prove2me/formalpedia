-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_quadraticGammaO_negTraceLambda
-- name    : OAI.ActualEisensteinCubic.quadraticGammaO_negTraceLambda
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:25:38.629976+00:00
-- url     : https://prove2.me/theorems/3112243c-9c8e-422e-9227-8ea103e1595a
-- title:
--   Actual Eisenstein Cubic: quadratic Gamma O neg Trace Lambda
-- statement:
--   The Actual Eisenstein Cubic construction uses the quadratic Gamma O neg Trace Lambda property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L33-L35
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L33-L35

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
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
open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE

theorem OAI.ActualEisensteinCubic.quadraticGammaO_negTraceLambda :
    quadraticGammaO (-traceLambda) (neg_ne_zero.mpr traceLambda_ne_zero) =
      quadraticGammaNegTraceLambda := by sorry
