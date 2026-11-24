-- Prove2me | Theorems.Thm_GaussianPerimeter_measurableSet_capCone
-- name    : GaussianPerimeter.measurableSet_capCone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:08:28.240799+00:00
-- url     : https://prove2.me/theorems/b776cfcc-5c87-4e46-99bb-d8551cd638b1
-- title:
--   Gaussian Perimeter: measurable Set cap Cone
-- statement:
--   The Gaussian Perimeter construction uses the measurable Set cap Cone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Sphere.lean#L119-L126
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Sphere.lean#L119-L126

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
omit [FiniteDimensional ℝ E]

theorem GaussianPerimeter.measurableSet_capCone (v : E) (t : ℝ) : MeasurableSet (capCone v t) := by sorry
