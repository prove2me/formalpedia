-- Prove2me | Theorems.Thm_GaussianPerimeter_one_sub_capTail_le_uniformSphere
-- name    : GaussianPerimeter.one_sub_capTail_le_uniformSphere
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T11:05:44.23143+00:00
-- url     : https://prove2.me/theorems/0f5bedb5-3922-4432-9419-f7a876e8a1fe
-- title:
--   Gaussian Perimeter: one sub cap Tail le uniform Sphere
-- statement:
--   The probability of passing an inner-product constraint from the facet computation.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/SphereCap.lean#L47-L64
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/SphereCap.lean#L47-L64

module
public import Definitions.Def_GaussianPerimeter_SphereSections
public import Definitions.Def_GaussianPerimeter_CapAsymptotics
public import Definitions.Def_GaussianPerimeter_SphereCap
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
open GaussianPerimeter

theorem GaussianPerimeter.one_sub_capTail_le_uniformSphere (n : ℕ) (hn : 2 ≤ n)
    {v : EuclideanSpace ℝ (Fin (n + 1))} (hv : ‖v‖ = 1) {ρ R : ℝ}
    (hρ : 0 < ρ) (hR : ρ < R) :
    1 - ENNReal.ofReal (capTail n (ρ / R)) ≤
      uniformSphere (EuclideanSpace ℝ (Fin (n + 1)))
        {u | ⟪R • v, (u : EuclideanSpace ℝ (Fin (n + 1)))⟫ < ρ} := by sorry
