-- Prove2me | Theorems.Thm_GaussianPerimeter_facetAcceptanceProbability_eq
-- name    : GaussianPerimeter.facetAcceptanceProbability_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:19:13.235553+00:00
-- url     : https://prove2.me/theorems/162474a8-4785-4ded-9a91-6ebd456ba324
-- title:
--   Gaussian Perimeter: facet Acceptance Probability eq
-- statement:
--   The Gaussian Perimeter construction uses the facet Acceptance Probability eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Averaging.lean#L40-L49
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Averaging.lean#L40-L49

module
public import Definitions.Def_GaussianPerimeter_Geometry
public import Definitions.Def_GaussianPerimeter_Sphere
public import Definitions.Def_GaussianPerimeter_Averaging
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Function
open scoped ENNReal RealInnerProductSpace InnerProductSpace
open GaussianPerimeter
local notation "Euc" k => EuclideanSpace ℝ (Fin k)
local notation "UnitSphere" k => Metric.sphere (0 : Euc (k + 1)) 1

theorem GaussianPerimeter.facetAcceptanceProbability_eq (k : ℕ) (ρ r : ℝ)
    (h : 0 < Real.sqrt (ρ ^ 2 + r ^ 2)) :
    facetAcceptanceProbability k ρ r = uniformSphere (Euc (k + 1))
      {v | ⟪(EuclideanSpace.basisFun (Fin (k + 1)) ℝ 0), v.val⟫_ℝ <
        ρ / Real.sqrt (ρ ^ 2 + r ^ 2)} := by sorry
