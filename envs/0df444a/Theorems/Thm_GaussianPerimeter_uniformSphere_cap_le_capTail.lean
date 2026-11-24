-- Prove2me | Theorems.Thm_GaussianPerimeter_uniformSphere_cap_le_capTail
-- name    : GaussianPerimeter.uniformSphere_cap_le_capTail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:05:33.360807+00:00
-- url     : https://prove2.me/theorems/c91b3eec-30f4-447b-b5e5-7860548a26b6
-- title:
--   Gaussian Perimeter: uniform Sphere cap le cap Tail
-- statement:
--   A uniform sphere sample lies above a threshold in a unit direction with
--   probability at most the one-coordinate cap tail.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/SphereCap.lean#L24-L43
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/SphereCap.lean#L24-L43

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

theorem GaussianPerimeter.uniformSphere_cap_le_capTail (n : ℕ) (hn : 2 ≤ n)
    {v : EuclideanSpace ℝ (Fin (n + 1))} (hv : ‖v‖ = 1) {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) :
    uniformSphere (EuclideanSpace ℝ (Fin (n + 1)))
      {u | t ≤ ⟪v, (u : EuclideanSpace ℝ (Fin (n + 1)))⟫} ≤ ENNReal.ofReal (capTail n t) := by sorry
