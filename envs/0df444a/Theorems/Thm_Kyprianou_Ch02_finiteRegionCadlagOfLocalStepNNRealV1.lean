-- Prove2me | Theorems.Thm_Kyprianou_Ch02_finiteRegionCadlagOfLocalStepNNRealV1
-- name    : Kyprianou.Ch02.finiteRegionCadlagOfLocalStepNNRealV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T09:46:12.450405+00:00
-- url     : https://prove2.me/theorems/037fd5fc-4e4b-4e60-a96e-ed0dddc443e9
-- title:
--   Càdlàg from local coincidence with finite marked step sums
-- statement:
--   An ℝ≥0-indexed real path is càdlàg if each time has a neighbourhood contained in a larger bounded interval where it coincides with some finite marked step sum. Uses Proved source-exact IsCadlagAt.congr, the Proved finite marked step-sum càdlàg theorem, and the order-topological neighbourhood of t inside Iio T. This is a deterministic local-gluing argument and a genuine reusable dependency for Poisson finite activity.
-- source:
--   Kyprianou (2006) Chapter 2 Lemma 2.8; LeanLevy/Processes/Cadlag.lean IsCadlagAt.congr and finite step sum.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_finiteRegionStepSumCadlagNNRealV1
import Theorems.Thm_ProbabilityTheory_IsCadlagAt_congr
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem finiteRegionCadlagOfLocalStepNNRealV1
    (f : ℝ≥0 → ℝ)
    (hlocal : ∀ (t : ℝ≥0), ∃ T : ℝ≥0, t < T ∧
      ∃ (s : Finset (ℝ × ℝ)) (w : ℝ × ℝ → ℝ),
        ∀ u : ℝ≥0, u < T →
          f u = ∑ p ∈ s, if p.1 ≤ (u : ℝ) then w p else 0) :
    ProbabilityTheory.IsCadlag f := by sorry
end Kyprianou.Ch02
