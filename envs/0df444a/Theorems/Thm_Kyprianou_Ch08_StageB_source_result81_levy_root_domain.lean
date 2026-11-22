-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_levy_root_domain
-- name    : Kyprianou.Ch08.StageB.source_result81_levy_root_domain
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:07:44.375611+00:00
-- url     : https://prove2.me/theorems/88aa77e2-4924-42e7-a415-7fcbc4e8ae14
-- title:
--   Right roots and transform domains for the Chapter 8 Lévy exponent
-- statement:
--   A spectrally negative Lévy process whose paths are not almost surely antitone has Laplace exponent zero at the origin and a largest nonnegative root at every nonnegative level. Its exponent strictly exceeds the given level exactly to the right of that root. An almost surely nonpositive increment law at every time would give antitone paths by stationarity, countably many clocks and right continuity. A positive increment with positive probability therefore forces the exponent unbounded above. Convexity and continuity then give the root description.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1, tilted descending potential. Reduction of 4c63d0ad-20de-450a-9ecd-09b666951d4c.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_levy_root_domain
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hnotneg : ¬ (∀ᵐ ω ∂P, Antitone (fun t : ℝ≥0 => A.X t ω))) :
    A.ψ 0 = 0 ∧ ∀ q : ℝ, 0 ≤ q → IsScaleTransformDomainBridge A.ψ q := by
  sorry
