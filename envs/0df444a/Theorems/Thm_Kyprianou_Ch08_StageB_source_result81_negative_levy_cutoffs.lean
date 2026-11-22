-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_negative_levy_cutoffs
-- name    : Kyprianou.Ch08.StageB.source_result81_negative_levy_cutoffs
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T20:23:36.583038+00:00
-- url     : https://prove2.me/theorems/95ed2134-a014-40d7-9f45-81d53605e260
-- title:
--   Negative Lévy cutoff restrictions are finite and exhaust integrable tests
-- statement:
--   Restrictions to y≤−1/(n+1) are finite by the Lévy small-jump bound. They converge against every integrable test of the original measure supported on negative arguments.
-- source:
--   Finite Lévy–Khintchine cutoff argument for Kyprianou (2006), Chapter 8, Theorem 8.1. Parent Prove2Me theorem 987aeaac-dbe6-4ff6-aca6-d87cd87bffde.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_negative_levy_cutoffs
    (ν : Measure ℝ) (hν : IsLevyMeasure ν) (hneg : ν (Ici (0 : ℝ)) = 0) :
    (∀ n : ℕ, IsFiniteMeasure (ν.restrict (Iic (-(((n : ℝ) + 1)⁻¹))))) ∧
    ∀ (G : Type) [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      (F : ℝ → G), Integrable F ν →
      Tendsto (fun n : ℕ => ∫ y in Iic (-(((n : ℝ) + 1)⁻¹)), F y ∂ν)
        atTop (nhds (∫ y, F y ∂ν)) := by
  sorry
