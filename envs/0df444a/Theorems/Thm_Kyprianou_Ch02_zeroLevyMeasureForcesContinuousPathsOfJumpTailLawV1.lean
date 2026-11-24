-- Prove2me | Theorems.Thm_Kyprianou_Ch02_zeroLevyMeasureForcesContinuousPathsOfJumpTailLawV1
-- name    : Kyprianou.Ch02.zeroLevyMeasureForcesContinuousPathsOfJumpTailLawV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T23:20:36.11425+00:00
-- url     : https://prove2.me/theorems/38b699fa-f3d4-4a7b-8ab2-d73f80950042
-- title:
--   Zero Lévy measure and the jump-tail law imply continuous càdlàg paths
-- statement:
--   Zero Lévy measure and the jump-tail law imply continuous càdlàg paths
-- source:
--   Kyprianou (2006), Exercise 2.7(b)

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem zeroLevyMeasureForcesContinuousPathsOfJumpTailLawV1
    (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (htail : ∀ (t : ℝ≥0) (threshold : ℝ), 0 < threshold →
      P {ω | ∃ s : ℝ≥0, 0 < s ∧ s ≤ t ∧
        ∃ l : ℝ,
          Tendsto (fun u => X u ω)
            (nhdsWithin s (Set.Iio s)) (nhds l) ∧
          threshold < |X s ω - l|} =
      ENNReal.ofReal (1 -
        Real.exp (-(t : ℝ) * (ν {x : ℝ | threshold < |x|}).toReal)))
    (hX : ProbabilityTheory.IsLevyProcess X P) (hzero : ν = 0) :
    ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => X t ω) := by sorry
end Kyprianou.Ch02
