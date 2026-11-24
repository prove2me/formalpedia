-- Prove2me | Theorems.Thm_GaussianPerimeter_uniformSphere_cap_eq_cone
-- name    : GaussianPerimeter.uniformSphere_cap_eq_cone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:09:14.579802+00:00
-- url     : https://prove2.me/theorems/769332cc-5d64-426f-b736-d2586c61c1a2
-- title:
--   Gaussian Perimeter: uniform Sphere cap eq cone
-- statement:
--   The Gaussian Perimeter construction uses the uniform Sphere cap eq cone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Sphere.lean#L128-L165
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Sphere.lean#L128-L165

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem GaussianPerimeter.uniformSphere_cap_eq_cone [Nontrivial E] (v : E) (t : ℝ) :
    uniformSphere E {u | t ≤ ⟪v, (u : E)⟫} =
      volume (capCone v t) / volume (Metric.ball (0 : E) 1) := by sorry
