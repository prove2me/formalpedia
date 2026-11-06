-- Prove2me | Theorems.Thm_OAI_RankTwoPoisson_schwartz_int_poisson
-- name    : OAI.RankTwoPoisson.schwartz_int_poisson
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:25:12.367542+00:00
-- url     : https://prove2.me/theorems/d8119dee-a489-4172-92e0-6b07615af3b9
-- title:
--   Rank Two Poisson: schwartz int poisson
-- statement:
--   The Rank Two Poisson construction uses the schwartz int poisson property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L524-L527
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L524-L527

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

theorem OAI.RankTwoPoisson.schwartz_int_poisson (f : 𝓢(ℝ, ℂ)) :
    (∑' n : ℤ, f (n : ℝ)) = ∑' n : ℤ, (𝓕 f) (n : ℝ) := by sorry
