-- Prove2me | Theorems.Thm_GaussianPerimeter_uniformSphere_inner_eq_of_norm_eq
-- name    : GaussianPerimeter.uniformSphere_inner_eq_of_norm_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:11:21.277832+00:00
-- url     : https://prove2.me/theorems/2a7fd23f-222b-4872-b51e-73361af565cb
-- title:
--   Gaussian Perimeter: uniform Sphere inner eq of norm eq
-- statement:
--   Tail probabilities of an inner product with a uniformly random unit
--   vector depend on the deterministic vector only through its norm.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Sphere.lean#L194-L208
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Sphere.lean#L194-L208

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

theorem GaussianPerimeter.uniformSphere_inner_eq_of_norm_eq {x y : E} (hxy : ‖x‖ = ‖y‖) (c : ℝ) :
    uniformSphere E {u | ⟪x, (u : E)⟫ < c} =
    uniformSphere E {u | ⟪y, (u : E)⟫ < c} := by sorry
