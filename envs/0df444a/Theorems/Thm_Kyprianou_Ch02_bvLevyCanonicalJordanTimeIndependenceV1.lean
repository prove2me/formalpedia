-- Prove2me | Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanTimeIndependenceV1
-- name    : Kyprianou.Ch02.bvLevyCanonicalJordanTimeIndependenceV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T23:20:37.6383+00:00
-- url     : https://prove2.me/theorems/aaa9dc1f-647e-4c4e-99cf-b85bb98e1b40
-- title:
--   Positive and negative Jordan variations are independent at each time
-- statement:
--   Within an equal-grid cell the positive and negative parts cannot both be positive, yielding exact single-cell Laplace factor 1-a-b. Taking n independent cells, the product limit factors because n a b tends to zero, as follows from finiteness of the two marginal variation limits. Laplace uniqueness on the nonnegative quadrant gives independence.
-- source:
--   Kyprianou (2006), Exercise 2.8; canonical Jordan variation increments.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.bvLevyCanonicalJordanTimeIndependenceV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hBV : ∀ᵐ ω ∂P,
      LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) :
    let V : ℝ≥0 → Ω → ℝ := fun t ω =>
      variationOnFromTo (fun s : ℝ≥0 => X s ω) Set.univ 0 t
    let Spos : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω + X t ω) / 2
    let Sneg : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω - X t ω) / 2
    ∀ t : ℝ≥0, ProbabilityTheory.IndepFun (Spos t) (Sneg t) P := by sorry
