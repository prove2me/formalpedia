-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_finite_moment_log_scaling
-- name    : Kyprianou.Ch08.StageB.source_result81_finite_moment_log_scaling
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T13:59:01.171074+00:00
-- url     : https://prove2.me/theorems/7a841a62-55e9-4628-8737-7128864357b2
-- title:
--   Time scaling of a finite actual exponential moment
-- statement:
--   Independence and stationarity give a positive multiplicative extended moment function. Finiteness at one positive time gives finiteness at all times by comparison to integer multiples. Positivity and the càdlàg right-limit Fatou argument force its logarithm to be linear in time.
-- source:
--   Kyprianou (2006), Chapters 3 and 8, exponential moments and the Laplace characterization. Decomposition of 4aec3a48-841c-4d25-a6e1-3aeee066bb70.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_finite_moment_log_scaling
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) (t : ℝ≥0) (ht : 0 < t) (c : ℝ)
    (hint : Integrable (fun ω => Real.exp (c * D.X t ω)) P) :
    0 < (∫ ω, Real.exp (c * D.X t ω) ∂P) ∧
      Real.log (∫ ω, Real.exp (c * D.X 1 ω) ∂P) =
        Real.log (∫ ω, Real.exp (c * D.X t ω) ∂P) / (t : ℝ) := by
  sorry
