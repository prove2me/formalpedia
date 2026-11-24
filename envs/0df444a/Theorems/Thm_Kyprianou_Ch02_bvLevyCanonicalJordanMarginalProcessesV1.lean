-- Prove2me | Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanMarginalProcessesV1
-- name    : Kyprianou.Ch02.bvLevyCanonicalJordanMarginalProcessesV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:15:14.901805+00:00
-- url     : https://prove2.me/theorems/36b316b1-ec6c-47c4-9f13-07c7a25011d1
-- title:
--   Canonical positive and negative variations are Lévy processes
-- statement:
--   On each deterministic interval, positive and negative variation increments are limits of sums of positive and negative increments on a refining dense grid. Stationarity and independent increments pass to these almost sure limits. Variation of a càdlàg locally BV path is càdlàg, and the origin is pointwise zero.
-- source:
--   Kyprianou (2006), Exercise 2.8. Canonical Jordan variation route via fine deterministic partitions, alternative to drift plus raw jump sums.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.bvLevyCanonicalJordanMarginalProcessesV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hBV : ∀ᵐ ω ∂P,
      LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) :
    let V : ℝ≥0 → Ω → ℝ := fun t ω =>
      variationOnFromTo (fun s : ℝ≥0 => X s ω) Set.univ 0 t
    let Spos : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω + X t ω) / 2
    let Sneg : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω - X t ω) / 2
    ProbabilityTheory.IsLevyProcess Spos P ∧
    ProbabilityTheory.IsLevyProcess Sneg P := by sorry
