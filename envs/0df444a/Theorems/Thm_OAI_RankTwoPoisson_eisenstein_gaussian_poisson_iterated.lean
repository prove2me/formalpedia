-- Prove2me | Theorems.Thm_OAI_RankTwoPoisson_eisenstein_gaussian_poisson_iterated
-- name    : OAI.RankTwoPoisson.eisenstein_gaussian_poisson_iterated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:25:24.535295+00:00
-- url     : https://prove2.me/theorems/0a037e1b-a355-4d8d-9be7-8d427ec057ec
-- title:
--   Rank Two Poisson: eisenstein gaussian poisson iterated
-- statement:
--   The Rank Two Poisson construction uses the eisenstein gaussian poisson iterated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L771-L811
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L771-L811

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
open OAI.RankTwoPoisson
open Real

theorem OAI.RankTwoPoisson.eisenstein_gaussian_poisson_iterated {t : ℝ} (ht : 0 < t) :
    (∑' z : ℤ × ℤ, eisGauss t z) =
      (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
        (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
        ∑' k : ℤ, ∑' l : ℤ, dualTerm t (k,l) := by sorry
