-- Prove2me | Theorems.Thm_OAI_GaussianAbelPartition_tsum_periodic_weighted_partition
-- name    : OAI.GaussianAbelPartition.tsum_periodic_weighted_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:25:00.223203+00:00
-- url     : https://prove2.me/theorems/45437bca-f2ed-44bb-8e58-6c90aecec131
-- title:
--   Gaussian Abel Partition: tsum periodic weighted partition
-- statement:
--   The Gaussian Abel Partition construction uses the tsum periodic weighted partition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L372-L388
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L372-L388

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
open OAI.GaussianAbelPartition

theorem OAI.GaussianAbelPartition.tsum_periodic_weighted_partition {A B : Type*} [Fintype B]
    (q : A → B) (P : B → ℂ) (W : A → ℂ)
    (hf : Summable (fun a => P (q a) * W a)) :
    (∑' a : A, P (q a) * W a) =
      ∑ b : B, P b * ∑' a : (q ⁻¹' {b}), W a.1 := by sorry
