-- Prove2me | Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanPairStationaryIncrementsV1
-- name    : Kyprianou.Ch02.bvLevyCanonicalJordanPairStationaryIncrementsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:20:31.633175+00:00
-- url     : https://prove2.me/theorems/293ca4e5-7a11-4753-bdd6-449020165339
-- title:
--   Canonical Jordan variation pair has stationary increments
-- statement:
--   For every fixed block length, the vector of original increments on an equally spaced grid has the same law regardless of the block start. Positive and negative grid sums thus have the same laws and converge almost surely to Jordan increments.
-- source:
--   Kyprianou (2006), Exercise 2.8; canonical Jordan variation increments.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.bvLevyCanonicalJordanPairStationaryIncrementsV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hBV : ∀ᵐ ω ∂P,
      LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) :
    let V : ℝ≥0 → Ω → ℝ := fun t ω =>
      variationOnFromTo (fun s : ℝ≥0 => X s ω) Set.univ 0 t
    let Spos : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω + X t ω) / 2
    let Sneg : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω - X t ω) / 2
    ProbabilityTheory.HasStationaryIncrements
      (fun t ω => (Spos t ω, Sneg t ω)) P := by sorry
