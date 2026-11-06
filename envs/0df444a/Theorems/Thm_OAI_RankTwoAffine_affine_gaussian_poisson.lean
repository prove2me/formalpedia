-- Prove2me | Theorems.Thm_OAI_RankTwoAffine_affine_gaussian_poisson
-- name    : OAI.RankTwoAffine.affine_gaussian_poisson
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:44:36.243564+00:00
-- url     : https://prove2.me/theorems/e140e5d0-bb7c-44f9-a626-7b243231a62c
-- title:
--   Rank Two Affine: affine gaussian poisson
-- statement:
--   The Rank Two Affine construction uses the affine gaussian poisson property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/BinaryGaussian.lean#L372-L420
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/BinaryGaussian.lean#L372-L420

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
open OAI.RankTwoAffine
open RankTwoComplex

theorem OAI.RankTwoAffine.affine_gaussian_poisson {a b d u v : ℂ}
    (ha : 0 < a.re) (hδ : 0 < (schur a b d).re)
    (hO : Summable (binaryGaussian a b d u v))
    (hM : Summable (firstGaussian a b d u v))
    (hD : Summable (dualGaussian a b d u v)) :
    (∑' z : ℤ × ℤ, binaryGaussian a b d u v z) =
      (1 / a ^ (1 / 2 : ℂ)) *
        (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ, dualGaussian a b d u v z := by sorry
