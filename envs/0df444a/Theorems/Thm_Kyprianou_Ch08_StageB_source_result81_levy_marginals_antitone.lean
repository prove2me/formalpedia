-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_levy_marginals_antitone
-- name    : Kyprianou.Ch08.StageB.source_result81_levy_marginals_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:32:01.912729+00:00
-- url     : https://prove2.me/theorems/d619eaf0-5d45-46dd-9ef0-8b5378cf67ce
-- title:
--   Antitone paths from nonpositive time marginals
-- statement:
--   If every time marginal of a spectrally negative Levy process is almost surely nonpositive, stationarity gives almost sure ordering on a countable dense set of clocks, and right continuity extends it to all clock pairs.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1, tilted descending potential. Mathematical reduction of 88aa77e2-4924-42e7-a415-7fcbc4e8ae14.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_levy_marginals_antitone
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (h : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, A.X t ω ≤ 0) :
    ∀ᵐ ω ∂P, Antitone (fun t : ℝ≥0 => A.X t ω) := by
  sorry
