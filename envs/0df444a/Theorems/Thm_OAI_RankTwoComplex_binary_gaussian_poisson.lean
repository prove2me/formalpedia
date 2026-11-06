-- Prove2me | Theorems.Thm_OAI_RankTwoComplex_binary_gaussian_poisson
-- name    : OAI.RankTwoComplex.binary_gaussian_poisson
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:44:43.215705+00:00
-- url     : https://prove2.me/theorems/578d2a0d-1664-40b3-9916-324f0190c13d
-- title:
--   Rank Two Complex: binary gaussian poisson
-- statement:
--   The Rank Two Complex construction uses the binary gaussian poisson property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/BinaryGaussian.lean#L165-L213
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/BinaryGaussian.lean#L165-L213

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
open OAI.RankTwoComplex
open Real

theorem OAI.RankTwoComplex.binary_gaussian_poisson {a b d : ℂ}
    (ha : 0 < a.re) (hδ : 0 < (schur a b d).re)
    (hO : Summable (binaryGaussian a b d))
    (hM : Summable (firstGaussian a b d))
    (hD : Summable (dualGaussian a b d)) :
    (∑' z : ℤ × ℤ, binaryGaussian a b d z) =
      (1 / a ^ (1 / 2 : ℂ)) *
        (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ, dualGaussian a b d z := by sorry
