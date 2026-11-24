-- Prove2me | Theorems.Thm_GaussianPerimeter_lintegral_independent_restrictions
-- name    : GaussianPerimeter.lintegral_independent_restrictions
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:11:00.511325+00:00
-- url     : https://prove2.me/theorems/1ddcbd5f-dd63-49bf-8925-a4185dccab2f
-- title:
--   Gaussian Perimeter: lintegral independent restrictions
-- statement:
--   Given one distinguished sample, each of the other independent samples
--   must belong to the same measurable set.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Sphere.lean#L17-L85
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Sphere.lean#L17-L85

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

theorem GaussianPerimeter.lintegral_independent_restrictions {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure B)
    [SFinite ν] {N : ℕ} (i : Fin (N + 1)) (weight : A → B → ℝ≥0∞)
    (accept : A → B → A → Prop)
    (hw : Measurable (uncurry weight))
    (ha : MeasurableSet {q : (A × B) × A | accept q.1.1 q.1.2 q.2}) :
    (∫⁻ u, ∫⁻ y, {u | ∀ j ≠ i, accept (u i) y (u j)}.indicator
      (fun u => weight (u i) y) u ∂ν ∂Measure.pi (fun _ : Fin (N + 1) => μ)) =
    ∫⁻ a, ∫⁻ y, μ {v | accept a y v} ^ N * weight a y ∂ν ∂μ := by sorry
