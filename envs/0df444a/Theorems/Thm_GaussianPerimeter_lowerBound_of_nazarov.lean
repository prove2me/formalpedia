-- Prove2me | Theorems.Thm_GaussianPerimeter_lowerBound_of_nazarov
-- name    : GaussianPerimeter.lowerBound_of_nazarov
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:57:37.119203+00:00
-- url     : https://prove2.me/theorems/5f85366e-b914-4dad-a815-92a5567483b7
-- title:
--   Gaussian Perimeter: lower Bound of nazarov
-- statement:
--   The integral expression of equation (14), given the expected-perimeter
--   bound for Nazarov's random polytope.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/NazarovLimit.lean#L73-L107
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/NazarovLimit.lean#L73-L107

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

theorem GaussianPerimeter.lowerBound_of_nazarov {a b W : ℝ} (ha : 0 < a) (hb : 0 < b) (hW : 0 ≤ W)
    (hPolytope : ∀ᶠ n in atTop,
      ENNReal.ofReal ((⌊b / capScale a n⌋₊ : ℝ) *
        (Real.exp (-(capRho a n ^ 2) / 2) / Real.sqrt (2 * Real.pi))) *
        (∫⁻ w in Set.Ioc (-W) W, ENNReal.ofReal
          (shiftedRadialDensity n w * (1 - shiftedCapTail a n w) ^ (⌊b / capScale a n⌋₊ - 1)))
        ≤ Γ (n + 1)) :
    ENNReal.ofReal ((b * a * Real.exp (-a ^ 4 / 4) / Real.sqrt Real.pi) *
      (∫ w in (-W)..W, Real.exp (-w ^ 2 - b * Real.exp (a ^ 2 * w)))) ≤
      liminf (fun n : ℕ => Γ n / ENNReal.ofReal ((n : ℝ) ^ (1 / 4 : ℝ))) atTop := by sorry
