-- Prove2me | Theorems.Thm_OAI_GaussianMoment_x_exp_neg_le
-- name    : OAI.GaussianMoment.x_exp_neg_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:47:56.97832+00:00
-- url     : https://prove2.me/theorems/ae1faf68-481b-445c-8c69-9f9fab334aad
-- title:
--   Gaussian Moment: x exp neg le
-- statement:
--   The Gaussian Moment construction uses the x exp neg le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/GaussianMoments.lean#L21-L34
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/GaussianMoments.lean#L21-L34

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
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
open Filter Real Asymptotics
open OAI.GaussianMoment

theorem OAI.GaussianMoment.x_exp_neg_le (x : ℝ) (_hx : 0 ≤ x) :
    x * Real.exp (-x) ≤ 2 * Real.exp (-(x / 2)) := by sorry
