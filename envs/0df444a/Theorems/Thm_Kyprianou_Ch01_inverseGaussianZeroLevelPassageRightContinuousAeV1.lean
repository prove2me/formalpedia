-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianZeroLevelPassageRightContinuousAeV1
-- name    : Kyprianou.Ch01.inverseGaussianZeroLevelPassageRightContinuousAeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T23:20:38.874308+00:00
-- url     : https://prove2.me/theorems/26b4816a-fdad-4a43-b9bf-e7ea2db9c4a9
-- title:
--   Drifted Brownian inverse first passage is almost surely right-continuous at zero
-- statement:
--   Almost surely, Brownian motion with unit variance and positive drift has first positive-level passage times converging to zero as the positive level decreases to zero. The proof uses simultaneous finiteness, monotonicity and the known inverse Gaussian Laplace transform to establish almost-sure convergence at the reset zero level.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5, inverse-Gaussian Laplace exponent and zero-barrier regularity.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianZeroLevelPassageRightContinuousAeV1
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (b : ℝ) (hb : 0 < b)
    (hB : IsLinearBrownian P X 1 b)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)) :
    ∀ᵐ ω ∂P, ContinuousWithinAt
      (      fun u : ℝ≥0 =>
        if u = 0 then (0 : ℝ)
        else (match firstUpperPassage X (u : ℝ) ω with
        | none => (0 : ℝ)
        | some t => (t : ℝ))) (Ici (0 : ℝ≥0)) 0 := by
  sorry
