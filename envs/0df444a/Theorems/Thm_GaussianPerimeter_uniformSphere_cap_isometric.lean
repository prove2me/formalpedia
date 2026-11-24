-- Prove2me | Theorems.Thm_GaussianPerimeter_uniformSphere_cap_isometric
-- name    : GaussianPerimeter.uniformSphere_cap_isometric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:09:08.477957+00:00
-- url     : https://prove2.me/theorems/cda5f736-240a-4baf-8f70-c728f9db5f26
-- title:
--   Gaussian Perimeter: uniform Sphere cap isometric
-- statement:
--   Orthogonal changes of variables preserve normalized spherical cap probabilities.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Sphere.lean#L178-L190
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Sphere.lean#L178-L190

module
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Definitions.Def_GaussianPerimeter_Sphere
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Function
open scoped ENNReal Pointwise RealInnerProductSpace
open GaussianPerimeter
local notation "UnitSphere" E => Metric.sphere (0 : E) 1
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] [Nontrivial F]

theorem GaussianPerimeter.uniformSphere_cap_isometric (e : E ≃ₗᵢ[ℝ] F) (x : E) (c : ℝ) :
    uniformSphere E {u | c ≤ ⟪x, (u : E)⟫} =
      uniformSphere F {u | c ≤ ⟪e x, (u : F)⟫} := by sorry
