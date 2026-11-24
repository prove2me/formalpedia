-- Prove2me | Theorems.Thm_GaussianPerimeter_tendsto_normalized_prefactor
-- name    : GaussianPerimeter.tendsto_normalized_prefactor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:44:51.376957+00:00
-- url     : https://prove2.me/theorems/2c8bb7f5-11cb-43b5-bedd-7d3256c77868
-- title:
--   Gaussian Perimeter: tendsto normalized prefactor
-- statement:
--   The exponential prefactor in the expectation, divided by its scale,
--   converges after normalization by the dimension's fourth root.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Scaling.lean#L44-L59
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Scaling.lean#L44-L59

module
public import Definitions.Def_GaussianPerimeter_Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Definitions.Def_GaussianPerimeter_Scaling
set_option autoImplicit true
@[expose] public section
public section
open Filter
open scoped Topology
open GaussianPerimeter

theorem GaussianPerimeter.tendsto_normalized_prefactor {s : ℕ → ℝ} {a b : ℝ}
    (hs : Tendsto s atTop (𝓝 0))
    (hpos : ∀ᶠ n in atTop, 0 < s n) (hb : 0 ≤ b)
    (hscale : ∀ᶠ n : ℕ in atTop,
      Real.exp (-(a * Real.sqrt (Real.sqrt n)) ^ 2 / 2) / Real.sqrt (2 * Real.pi) =
        s n * (a * Real.sqrt (Real.sqrt n)) * Real.exp (-a ^ 4 / 4)) :
    Tendsto (fun n : ℕ => (⌊b / s n⌋₊ : ℝ) *
      (Real.exp (-(a * Real.sqrt (Real.sqrt n)) ^ 2 / 2) / Real.sqrt (2 * Real.pi)) /
        (n + 1 : ℝ) ^ (1 / 4 : ℝ)) atTop (𝓝 (b * a * Real.exp (-a ^ 4 / 4))) := by sorry
