-- Prove2me | Theorems.Thm_OAI_CubeInversion_cube_coefficient_filter
-- name    : OAI.CubeInversion.cube_coefficient_filter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:12:22.37705+00:00
-- url     : https://prove2.me/theorems/da16a8ed-cf27-4614-bcbd-341c01f1461c
-- title:
--   Cube Inversion: cube coefficient filter
-- statement:
--   The Cube Inversion construction uses the cube coefficient filter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SexticNormalization.lean#L443-L470
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SexticNormalization.lean#L443-L470

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

theorem OAI.CubeInversion.cube_coefficient_filter
    (m : ℕ) (c W : ℕ → ℂ)
    (hc : ∀ a b, c (a * b) = c a * c b) :
    (∑ h ∈ m.divisors,
      (ArithmeticFunction.moebius h : ℂ) * c h * c (m / h) * W m) =
      if m = 1 then c m * W m else 0 := by sorry
