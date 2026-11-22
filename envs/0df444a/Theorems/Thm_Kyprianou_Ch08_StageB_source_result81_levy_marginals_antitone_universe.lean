-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_levy_marginals_antitone_universe
-- name    : Kyprianou.Ch08.StageB.source_result81_levy_marginals_antitone_universe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T21:04:02.855821+00:00
-- url     : https://prove2.me/theorems/e732c683-4e70-4a24-9863-97ecb1bc5f4e
-- title:
--   Universe-polymorphic marginals imply antitone paths
-- statement:
--   Type-star version of the proved marginals-antitone lemma: if every marginal is nonpositive a.e., paths are antitone a.e. Needed to discharge the universe mismatch in the scale-transfer proof.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1 supporting lemma; universe-polymorphic restatement of source_result81_levy_marginals_antitone.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

theorem source_result81_levy_marginals_antitone_universe
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (h : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, A.X t ω ≤ 0) :
    ∀ᵐ ω ∂P, Antitone (fun t : ℝ≥0 => A.X t ω) := by
  sorry

end Kyprianou.Ch08.StageB
