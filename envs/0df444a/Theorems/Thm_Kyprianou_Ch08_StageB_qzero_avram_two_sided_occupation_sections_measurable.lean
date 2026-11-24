-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_qzero_avram_two_sided_occupation_sections_measurable
-- name    : Kyprianou.Ch08.StageB.qzero_avram_two_sided_occupation_sections_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T02:54:00.843972+00:00
-- url     : https://prove2.me/theorems/52e1009e-fc99-4250-95c8-98e325713692
-- title:
--   Two-sided killed occupation sections in the Avram model
-- statement:
--   For the filtered Avram spectrally negative Levy model, the probability of occupying a Borel set before both strict passage clocks is a measurable function of nonnegative time.
-- source:
--   Source-faithful measurability obligation isolated from Kyprianou (2006), Chapter 8, proof of Corollary 8.8. It uses the accepted lower-clock identity, the upper-clock child, and product-section measurability.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_Kyprianou_Ch08_StageB_qzero_avram_upper_shifted_clock_eq
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_avram_source_lower_clock_eq
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_exp_clock_product_sections
import Theorems.Thm_AvramDividend_Classical_chat03_both_named_passage_clocks_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

theorem qzero_avram_two_sided_occupation_sections_measurable :
∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 mΩ)
    (X : AvramDividend.Classical.SpectrallyNegativeLevy P F),
    ∀ (a x : ℝ), 0 < a → 0 ≤ x → x ≤ a →
    ∀ (A : Set ℝ), MeasurableSet A →
    Measurable (fun t : ℝ≥0 =>
      P {ω | (t : WithTop ℝ≥0) <
        min (tauMinus (shifted X.X x) 0 ω)
          (tauPlus (shifted X.X x) a ω) ∧
        shifted X.X x t ω ∈ A})
:= by
  sorry

end Kyprianou.Ch08.StageB
