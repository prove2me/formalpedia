-- Prove2me | Theorems.Thm_OAI_GaussianAbelPartition_tsum_by_finite_fibers
-- name    : OAI.GaussianAbelPartition.tsum_by_finite_fibers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:25:00.617207+00:00
-- url     : https://prove2.me/theorems/1774088f-4c5d-478f-bb22-02408a5afbd5
-- title:
--   Gaussian Abel Partition: tsum by finite fibers
-- statement:
--   The Gaussian Abel Partition construction uses the tsum by finite fibers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L365-L370
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L365-L370

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

theorem OAI.GaussianAbelPartition.tsum_by_finite_fibers {A B : Type*} [Fintype B]
    (q : A → B) (f : A → ℂ) (hf : Summable f) :
    (∑' a : A, f a) =
      ∑ b : B, ∑' a : (q ⁻¹' {b}), f a.1 := by sorry
