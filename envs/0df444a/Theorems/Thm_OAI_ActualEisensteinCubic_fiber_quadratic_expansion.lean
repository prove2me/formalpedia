-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_fiber_quadratic_expansion
-- name    : OAI.ActualEisensteinCubic.fiber_quadratic_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:44:50.825342+00:00
-- url     : https://prove2.me/theorems/9e2c688a-b646-40e3-ba64-a2c54551a58e
-- title:
--   Actual Eisenstein Cubic: fiber quadratic expansion
-- statement:
--   The Actual Eisenstein Cubic construction uses the fiber quadratic expansion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/BinaryGaussian.lean#L456-L466
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/BinaryGaussian.lean#L456-L466

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

theorem OAI.ActualEisensteinCubic.fiber_quadratic_expansion (a b x y m n : ℤ) :
    let q := a*a-a*b+b*b
    let X := x+a*m-b*n
    let Y := y+b*m+(a-b)*n
    X*X-X*Y+Y*Y =
      q*(m*m-m*n+n*n) +
      ((2*a-b)*x+(2*b-a)*y)*m +
      (-(a+b)*x+(2*a-b)*y)*n +
      (x*x-x*y+y*y) := by sorry
