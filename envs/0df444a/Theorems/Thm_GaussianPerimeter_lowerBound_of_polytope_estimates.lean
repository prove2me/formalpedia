-- Prove2me | Theorems.Thm_GaussianPerimeter_lowerBound_of_polytope_estimates
-- name    : GaussianPerimeter.lowerBound_of_polytope_estimates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:44:53.034147+00:00
-- url     : https://prove2.me/theorems/6c83b7c2-976b-493e-9c8f-c9352016c77c
-- title:
--   Gaussian Perimeter: lower Bound of polytope estimates
-- statement:
--   Turning the expected perimeter inequality for the random polytope into an
--   asymptotic bound, given the pointwise radial and cap estimates.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/LimitBound.lean#L16-L111
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/LimitBound.lean#L16-L111

module
public import Definitions.Def_GaussianPerimeter_Definitions
public import Definitions.Def_GaussianPerimeter_Scaling
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Definitions.Def_GaussianPerimeter_LimitBound
set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory
open scoped ENNReal Topology
open GaussianPerimeter

theorem GaussianPerimeter.lowerBound_of_polytope_estimates {a b W : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hW : 0 ≤ W)
    {s : ℕ → ℝ} {radial p q : ℕ → ℝ → ℝ}
    (hs : Tendsto s atTop (𝓝 0)) (hspos : ∀ᶠ n in atTop, 0 < s n)
    (hscale : ∀ᶠ n : ℕ in atTop,
      Real.exp (-(a * Real.sqrt (Real.sqrt n)) ^ 2 / 2) / Real.sqrt (2 * Real.pi) =
        s n * (a * Real.sqrt (Real.sqrt n)) * Real.exp (-a ^ 4 / 4))
    (hRadial : ∀ w, Tendsto (fun n => radial n w) atTop
      (𝓝 (Real.exp (-w ^ 2) / Real.sqrt Real.pi)))
    (hRadialNonneg : ∀ n w, 0 ≤ radial n w)
    (hCap : ∀ w, Tendsto (fun n => q n w / s n) atTop (𝓝 (Real.exp (a ^ 2 * w))))
    (hCapLe : ∀ w, ∀ᶠ n in atTop, p n w ≤ q n w)
    (hMeas : ∀ n, Measurable (fun w => ENNReal.ofReal
      (radial n w * (1 - p n w) ^ (⌊b / s n⌋₊ - 1))))
    (hPolytope : ∀ᶠ n in atTop,
      ENNReal.ofReal ((⌊b / s n⌋₊ : ℝ) *
        (Real.exp (-(a * Real.sqrt (Real.sqrt n)) ^ 2 / 2) / Real.sqrt (2 * Real.pi))) *
        (∫⁻ w in Set.Ioc (-W) W, ENNReal.ofReal
          (radial n w * (1 - p n w) ^ (⌊b / s n⌋₊ - 1))) ≤ Γ (n + 1)) :
    ENNReal.ofReal ((b * a * Real.exp (-a ^ 4 / 4) / Real.sqrt Real.pi) *
      (∫ w in (-W)..W, Real.exp (-w ^ 2 - b * Real.exp (a ^ 2 * w)))) ≤
      liminf (fun n : ℕ => Γ n / ENNReal.ofReal ((n : ℝ) ^ (1 / 4 : ℝ))) atTop := by sorry
