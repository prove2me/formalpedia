-- Prove2me | Theorems.Thm_GaussianPerimeter_facet_lintegral_sum_le_gaussianPerimeter
-- name    : GaussianPerimeter.facet_lintegral_sum_le_gaussianPerimeter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:10:54.461029+00:00
-- url     : https://prove2.me/theorems/943c4731-3ec7-48eb-bed9-7e6c53963f62
-- title:
--   Gaussian Perimeter: facet lintegral sum le gaussian Perimeter
-- statement:
--   The sum of the Gaussian integrals over the strict facets is bounded by the
--   Gaussian perimeter, provided the chosen Hausdorff normalization dominates
--   Lebesgue measure on the model hyperplane.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Geometry.lean#L182-L234
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Geometry.lean#L182-L234

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
variable {k : ℕ} {ι : Type*}

theorem GaussianPerimeter.facet_lintegral_sum_le_gaussianPerimeter [Fintype ι] (u : ι → Euc (k + 1))
    (hu : ∀ i, ‖u i‖ = 1) (ρ : ℝ)
    (hvolume : (volume : Measure (Euc k)) ≤
      (volume (Metric.ball (0 : Euc k) 1) / (2 : ℝ≥0∞) ^ k) • μH[(k : ℝ)]) :
    (∑ i, ∫⁻ y in {y | ∀ j ≠ i, ⟪u j, facetEmbedding (u i) (hu i) ρ y⟫_ℝ < ρ},
      ENNReal.ofReal ((2 * Real.pi) ^ (-(k + 1 : ℝ) / 2) *
        Real.exp (-(ρ ^ 2 + ‖y‖ ^ 2) / 2))) ≤
      gaussianPerimeter (halfspaceIntersection u ρ) := by sorry
