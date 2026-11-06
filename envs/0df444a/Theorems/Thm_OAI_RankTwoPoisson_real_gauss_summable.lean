-- Prove2me | Theorems.Thm_OAI_RankTwoPoisson_real_gauss_summable
-- name    : OAI.RankTwoPoisson.real_gauss_summable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:25:35.632335+00:00
-- url     : https://prove2.me/theorems/0a1179ea-a4b2-47a3-9bb9-2115391fdb00
-- title:
--   Rank Two Poisson: real gauss summable
-- statement:
--   The Rank Two Poisson construction uses the real gauss summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L583-L587
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L583-L587

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

theorem OAI.RankTwoPoisson.real_gauss_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℤ => Real.exp (-Real.pi * t * (n : ℝ) ^ 2)) := by sorry
