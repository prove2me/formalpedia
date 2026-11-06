-- Prove2me | Theorems.Thm_OAI_RankTwoPoisson_schwartz_int_summable
-- name    : OAI.RankTwoPoisson.schwartz_int_summable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:25:23.329133+00:00
-- url     : https://prove2.me/theorems/9af86f85-6b23-41a0-9ff9-237443ab9354
-- title:
--   Rank Two Poisson: schwartz int summable
-- statement:
--   The Rank Two Poisson construction uses the schwartz int summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L515-L518
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L515-L518

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

theorem OAI.RankTwoPoisson.schwartz_int_summable (f : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℤ => f (n : ℝ)) := by sorry
