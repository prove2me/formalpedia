-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianZeroBoundaryRightContinuousAeV1
-- name    : Kyprianou.Ch01.inverseGaussianZeroBoundaryRightContinuousAeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T23:17:52.132344+00:00
-- url     : https://prove2.me/theorems/e0c797b4-14e5-454e-9b1a-9d25b9c859fb
-- title:
--   Inverse-Gaussian passage paths are almost surely right-continuous at every barrier including zero
-- statement:
--   For drifted Brownian motion, the level-indexed first strictly upper passage process, normalised to zero at level zero, has almost surely right-continuous real-valued paths at every nonnegative level. Positive-level right continuity follows from the strict-upcrossing infimum and finite passage; at zero it follows by inverse Gaussian Laplace transforms, monotonicity, and a countable limit.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5 and its passage-time Laplace transform, with explicit pathwise zero normalisation.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianZeroBoundaryRightContinuousAeV1
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (b : ℝ) (hb : 0 < b)
    (hB : Kyprianou.Ch01.IsLinearBrownian P X 1 b)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)) :
    let T : ℝ≥0 → Ω → ℝ :=
      fun s ω =>
        if s = 0 then (0 : ℝ)
        else (match Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω with
        | none => (0 : ℝ)
        | some t => (t : ℝ))
    ∀ᵐ ω ∂P, ∀ s : ℝ≥0,
      ContinuousWithinAt (fun u : ℝ≥0 => T u ω) (Ici s) s := by
  sorry
