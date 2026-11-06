-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_fiber_norm_sq
-- name    : OAI.ActualEisensteinCubic.eisEmbedding_fiber_norm_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:44:37.779315+00:00
-- url     : https://prove2.me/theorems/d9facf17-e07d-4f17-b530-a2dab314692a
-- title:
--   Actual Eisenstein Cubic: eis Embedding fiber norm sq
-- statement:
--   The Actual Eisenstein Cubic construction uses the eis Embedding fiber norm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/BinaryGaussian.lean#L468-L478
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/BinaryGaussian.lean#L468-L478

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

theorem OAI.ActualEisensteinCubic.eisEmbedding_fiber_norm_sq (a b x y m n : ℤ) :
    ‖eisEmbedding
      (ActualEisensteinCoordinates.eval x y +
        ActualEisensteinCoordinates.eval a b *
          ActualEisensteinCoordinates.eval m n)‖ ^ 2 =
      ((a*a-a*b+b*b)*(m*m-m*n+n*n) +
      ((2*a-b)*x+(2*b-a)*y)*m +
      (-(a+b)*x+(2*a-b)*y)*n +
      (x*x-x*y+y*y) : ℤ) := by sorry
