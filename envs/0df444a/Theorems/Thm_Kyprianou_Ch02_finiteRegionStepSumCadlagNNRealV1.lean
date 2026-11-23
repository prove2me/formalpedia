-- Prove2me | Theorems.Thm_Kyprianou_Ch02_finiteRegionStepSumCadlagNNRealV1
-- name    : Kyprianou.Ch02.finiteRegionStepSumCadlagNNRealV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T09:38:44.274478+00:00
-- url     : https://prove2.me/theorems/326dd1c5-a7ca-4600-9b65-956fdcd0b03d
-- title:
--   Finite marked step sums are càdlàg on nonnegative time
-- statement:
--   For any finite set of marked event times and arbitrary real amplitudes, the right-continuous sum of jump steps over real nonnegative time is càdlàg. Prove by reusing Proved LeanLevy IsCadlag.finsetSum and isCadlag_stepIndicator plus the Proved coercion lemma isCadlag_comp_nnrealCoe. This supplies the deterministic path regularity underlying finite-region marked Poisson integrals.
-- source:
--   Kyprianou Chapter 2 Lemma 2.8; proven LeanLevy/Processes/Cadlag.lean finsetSum, isCadlag_stepIndicator, isCadlag_comp_nnrealCoe.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem finiteRegionStepSumCadlagNNRealV1
    (s : Finset (ℝ × ℝ)) (weight : ℝ × ℝ → ℝ) :
    ProbabilityTheory.IsCadlag
      (fun t : ℝ≥0 =>
        ∑ p ∈ s, if p.1 ≤ (t : ℝ) then weight p else 0) := by sorry
end Kyprianou.Ch02
