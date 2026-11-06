-- Prove2me | Theorems.Thm_OAI_RankTwoPoisson_diagonal_gaussian_poisson
-- name    : OAI.RankTwoPoisson.diagonal_gaussian_poisson
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:26:07.212418+00:00
-- url     : https://prove2.me/theorems/e31f98e4-17a3-47f3-9687-76ab3326cc78
-- title:
--   Rank Two Poisson: diagonal gaussian poisson
-- statement:
--   The Rank Two Poisson construction uses the diagonal gaussian poisson property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L565-L581
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L565-L581

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

theorem OAI.RankTwoPoisson.diagonal_gaussian_poisson {a b : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re)
    (hai : 0 < (a⁻¹).re) (hbi : 0 < (b⁻¹).re) :
    (∑' z : ℤ × ℤ, cg a z.1 * cg b z.2) =
      (1 / a ^ (1 / 2 : ℂ)) * (1 / b ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ, cg a⁻¹ z.1 * cg b⁻¹ z.2 := by sorry
