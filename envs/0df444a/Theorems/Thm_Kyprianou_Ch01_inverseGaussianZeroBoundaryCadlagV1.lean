-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianZeroBoundaryCadlagV1
-- name    : Kyprianou.Ch01.inverseGaussianZeroBoundaryCadlagV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T23:03:31.41537+00:00
-- url     : https://prove2.me/theorems/993e404d-606b-476f-a429-817a6684a11f
-- title:
--   §1.2.5: Brownian passage subordinator Cadlag
-- statement:
--   Almost every Brownian path with positive drift crosses all positive levels. Its strictly-upper first-passage inverse, normalised to zero at level zero, is right-continuous with left limits in the level variable.
-- source:
--   Kyprianou (2006), Chapter 1, §1.2.5, pp. 8–9, equation (1.4), and the strong Markov first-passage construction.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open scoped Classical
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianZeroBoundaryCadlagV1
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
    ∀ᵐ ω ∂P, IsCadlag (fun t : ℝ≥0 => T t ω) := by
  sorry
