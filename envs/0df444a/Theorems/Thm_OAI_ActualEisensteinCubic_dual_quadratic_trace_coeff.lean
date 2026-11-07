-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_dual_quadratic_trace_coeff
-- name    : OAI.ActualEisensteinCubic.dual_quadratic_trace_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:25:16.89531+00:00
-- url     : https://prove2.me/theorems/16199eb4-bf8b-41b1-a8b9-f180346c5e0f
-- title:
--   Actual Eisenstein Cubic: dual quadratic trace coeff
-- statement:
--   The Actual Eisenstein Cubic construction uses the dual quadratic trace coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/OscillatoryGaussian.lean#L104-L112
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/OscillatoryGaussian.lean#L104-L112

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
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
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex

theorem OAI.ActualEisensteinCubic.dual_quadratic_trace_coeff (a b k l : ℤ) :
    (ActualEisensteinCoordinates.coords
      (ActualEisensteinCoordinates.eval a b *
        (ActualEisensteinCoordinates.eval (k+l) k)^2)).2 =
      (a-b)*k^2+2*a*k*l+b*l^2 := by sorry
