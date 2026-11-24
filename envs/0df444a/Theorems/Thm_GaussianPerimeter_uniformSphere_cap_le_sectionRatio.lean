-- Prove2me | Theorems.Thm_GaussianPerimeter_uniformSphere_cap_le_sectionRatio
-- name    : GaussianPerimeter.uniformSphere_cap_le_sectionRatio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:03:38.123297+00:00
-- url     : https://prove2.me/theorems/8056cc56-3e1f-4777-8aad-d422d6c99e09
-- title:
--   Gaussian Perimeter: uniform Sphere cap le section Ratio
-- statement:
--   A spherical cap probability bounded through the two sections of the cone's unit ball.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/SphereSections.lean#L170-L199
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/SphereSections.lean#L170-L199

module
public import Definitions.Def_GaussianPerimeter_Sphere
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Definitions.Def_GaussianPerimeter_SphereSections
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
open GaussianPerimeter
local notation "Euc" n => EuclideanSpace ℝ (Fin n)
local notation "W" n => WithLp 2 (ℝ × Euc n)
local notation "axis" n => (WithLp.toLp 2 ((1 : ℝ), (0 : Euc n)))

theorem GaussianPerimeter.uniformSphere_cap_le_sectionRatio (n : ℕ) [NeZero n] {v : Euc (n + 1)}
    (hv : ‖v‖ = 1) {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) :
    uniformSphere (Euc (n + 1)) {u | t ≤ ⟪v, (u : Euc (n + 1))⟫} ≤
      ENNReal.ofReal (t / ((n : ℝ) + 1) * (Real.sqrt (1 - t ^ 2)) ^ n +
        ∫ x in t..1, (Real.sqrt (1 - x ^ 2)) ^ n) /
      ENNReal.ofReal (∫ x in (-1 : ℝ)..1, (Real.sqrt (1 - x ^ 2)) ^ n) := by sorry
