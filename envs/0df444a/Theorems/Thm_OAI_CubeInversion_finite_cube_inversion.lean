-- Prove2me | Theorems.Thm_OAI_CubeInversion_finite_cube_inversion
-- name    : OAI.CubeInversion.finite_cube_inversion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:12:21.330494+00:00
-- url     : https://prove2.me/theorems/f762c341-a5d9-4182-a6e8-b96e31c49d86
-- title:
--   Cube Inversion: finite cube inversion
-- statement:
--   The Cube Inversion construction uses the finite cube inversion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SexticNormalization.lean#L472-L479
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SexticNormalization.lean#L472-L479

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

theorem OAI.CubeInversion.finite_cube_inversion
    (S : Finset ℕ) (hS : 1 ∈ S) (c W : ℕ → ℂ)
    (hc : ∀ a b, c (a * b) = c a * c b) :
    (∑ m ∈ S, ∑ h ∈ m.divisors,
      (ArithmeticFunction.moebius h : ℂ) * c h * c (m / h) * W m) =
        c 1 * W 1 := by sorry
