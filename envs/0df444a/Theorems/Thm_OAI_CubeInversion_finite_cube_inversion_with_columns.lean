-- Prove2me | Theorems.Thm_OAI_CubeInversion_finite_cube_inversion_with_columns
-- name    : OAI.CubeInversion.finite_cube_inversion_with_columns
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:12:26.511902+00:00
-- url     : https://prove2.me/theorems/742bee78-797a-49eb-acf0-68f87a7a04fa
-- title:
--   Cube Inversion: finite cube inversion with columns
-- statement:
--   The Cube Inversion construction uses the finite cube inversion with columns property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SexticNormalization.lean#L481-L491
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SexticNormalization.lean#L481-L491

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
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
open OAI.CubeInversion

theorem OAI.CubeInversion.finite_cube_inversion_with_columns {N : Type*} [DecidableEq N]
    (columns : Finset N) (S : Finset ℕ) (hS : 1 ∈ S)
    (a : N → ℂ) (c : ℕ → ℂ) (W : N → ℕ → ℂ)
    (hc : ∀ x y, c (x * y) = c x * c y) :
    (∑ n ∈ columns, a n *
      (∑ m ∈ S, ∑ h ∈ m.divisors,
        (ArithmeticFunction.moebius h : ℂ) * c h * c (m / h) * W n m)) =
      ∑ n ∈ columns, a n * (c 1 * W n 1) := by sorry
