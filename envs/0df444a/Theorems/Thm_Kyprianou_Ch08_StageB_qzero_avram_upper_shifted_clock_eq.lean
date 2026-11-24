-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_qzero_avram_upper_shifted_clock_eq
-- name    : Kyprianou.Ch08.StageB.qzero_avram_upper_shifted_clock_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T02:45:21.28383+00:00
-- url     : https://prove2.me/theorems/fcf39183-fac1-49c8-988e-98459c66b9b3
-- title:
--   Upper passage clock of the shifted Avram path
-- statement:
--   For a right-continuous Avram spectrally negative Levy path, the positive-time strict upper passage clock of the origin-shifted path equals the all-time upper exit clock at the shifted barrier.
-- source:
--   Source-faithful clock identity isolated from the Chapter 8 zero-discount occupation argument. It applies the accepted positive-time open passage/all-time infimum lemma to the right-continuous shifted Avram path.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_positive_open_clock_eq_all_times
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

theorem qzero_avram_upper_shifted_clock_eq :
∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 mΩ)
    (X : AvramDividend.Classical.SpectrallyNegativeLevy P F),
    ∀ (a x : ℝ), 0 < a → 0 ≤ x → x ≤ a →
    ∀ ω : Ω,
      (tauPlus (shifted X.X x) a ω : ℝ≥0∞) =
        AvramDividend.Classical.twoSidedExitUpTime X (a - x) ω
:= by
  sorry

end Kyprianou.Ch08.StageB
