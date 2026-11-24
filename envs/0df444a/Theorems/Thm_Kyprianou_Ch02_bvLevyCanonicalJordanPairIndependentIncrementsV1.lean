-- Prove2me | Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanPairIndependentIncrementsV1
-- name    : Kyprianou.Ch02.bvLevyCanonicalJordanPairIndependentIncrementsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:20:35.846177+00:00
-- url     : https://prove2.me/theorems/42ba817c-659a-4d15-8d64-4c8837a5876d
-- title:
--   Canonical Jordan variation pair has independent increments
-- statement:
--   Each consecutive pair of Jordan increments equals the limit of the positive and negative increment sums over refining partitions of that interval. Distinct interval blocks have independent increments on every grid; independence is preserved under almost sure limits.
-- source:
--   Kyprianou (2006), Exercise 2.8; canonical Jordan variation increments.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.bvLevyCanonicalJordanPairIndependentIncrementsV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hBV : ∀ᵐ ω ∂P,
      LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) :
    let V : ℝ≥0 → Ω → ℝ := fun t ω =>
      variationOnFromTo (fun s : ℝ≥0 => X s ω) Set.univ 0 t
    let Spos : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω + X t ω) / 2
    let Sneg : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω - X t ω) / 2
    ProbabilityTheory.HasIndependentIncrements
      (fun t ω => (Spos t ω, Sneg t ω)) P := by sorry
