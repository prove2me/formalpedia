-- Prove2me | Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanTimeLaplaceFactorV1
-- name    : Kyprianou.Ch02.bvLevyCanonicalJordanTimeLaplaceFactorV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:04:19.06374+00:00
-- url     : https://prove2.me/theorems/2c931f98-3fb4-4dc3-8e04-ae2ad1efcd07
-- title:
--   Jordan coordinates have factorising joint one-time Laplace transforms
-- statement:
--   The positive and negative equal-grid sums converge almost surely to Jordan components. Their bounded Laplace expectations converge, the marginal limits are strictly positive, and the disjoint-cell identity plus scalar power factorisation gives the joint limit.
-- source:
--   Kyprianou (2006), Exercise 2.8: Laplace factorisation of positive and negative variation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.bvLevyCanonicalJordanTimeLaplaceFactorV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hBV : ∀ᵐ ω ∂P, LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) :
    let V : ℝ≥0 → Ω → ℝ := fun t ω =>
      variationOnFromTo (fun s => X s ω) Set.univ 0 t
    let A : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω+X t ω)/2
    let B : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω-X t ω)/2
    ∀ t : ℝ≥0, ∀ u v : ℝ, 0 < u → 0 < v →
      (∫ ω, Real.exp (-(u*A t ω+v*B t ω)) ∂P) =
      (∫ ω, Real.exp (-(u*A t ω)) ∂P)*(∫ ω, Real.exp (-(v*B t ω)) ∂P) := by sorry
