-- Prove2me | Theorems.Thm_GaussianPerimeter_capScale_mul_density
-- name    : GaussianPerimeter.capScale_mul_density
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:55:43.979171+00:00
-- url     : https://prove2.me/theorems/7e47e472-78db-4219-945e-ea1293558559
-- title:
--   Gaussian Perimeter: cap Scale mul density
-- statement:
--   The Gaussian Perimeter construction uses the cap Scale mul density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/NazarovLimit.lean#L32-L43
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/NazarovLimit.lean#L32-L43

module
public import Definitions.Def_GaussianPerimeter_LimitBound
public import Definitions.Def_GaussianPerimeter_CapAsymptotics
public import Definitions.Def_GaussianPerimeter_Radial
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Definitions.Def_GaussianPerimeter_NazarovLimit
set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory
open scoped ENNReal Topology
open GaussianPerimeter

theorem GaussianPerimeter.capScale_mul_density {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n) :
    Real.exp (-(capRho a n ^ 2) / 2) / Real.sqrt (2 * Real.pi) =
      capScale a n * capRho a n * Real.exp (-a ^ 4 / 4) := by sorry
