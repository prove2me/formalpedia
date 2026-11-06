-- Prove2me | Theorems.Thm_OAI_RankTwoPoisson_eis_gauss_summable
-- name    : OAI.RankTwoPoisson.eis_gauss_summable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:24:54.812208+00:00
-- url     : https://prove2.me/theorems/1d95c118-5c4a-4d09-945d-f8494430dc2a
-- title:
--   Rank Two Poisson: eis gauss summable
-- statement:
--   The Rank Two Poisson construction uses the eis gauss summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L600-L618
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L600-L618

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

theorem OAI.RankTwoPoisson.eis_gauss_summable {t : ℝ} (ht : 0 < t) :
    Summable (eisGauss t) := by sorry
