-- Prove2me | Theorems.Thm_GaussianPerimeter_measurable_facetEmbedding
-- name    : GaussianPerimeter.measurable_facetEmbedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:09:57.527803+00:00
-- url     : https://prove2.me/theorems/ef2d4d90-b5fd-46c4-bb91-5f1be4923206
-- title:
--   Gaussian Perimeter: measurable facet Embedding
-- statement:
--   The hyperplane coordinates depend measurably on the normal and tangent coordinates.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Geometry.lean#L62-L90
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Geometry.lean#L62-L90

module
public import Definitions.Def_GaussianPerimeter_Definitions
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Definitions.Def_GaussianPerimeter_Geometry
set_option autoImplicit true
@[expose] public section
public section
open Function Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal InnerProductSpace RealInnerProductSpace Function
open GaussianPerimeter
local notation "Euc" k => EuclideanSpace ℝ (Fin k)

theorem GaussianPerimeter.measurable_facetEmbedding {k : ℕ} (ρ : ℝ) :
    Measurable (fun p : {u : Euc (k + 1) // ‖u‖ = 1} × Euc k =>
      facetEmbedding p.1.1 p.1.2 ρ p.2) := by sorry
