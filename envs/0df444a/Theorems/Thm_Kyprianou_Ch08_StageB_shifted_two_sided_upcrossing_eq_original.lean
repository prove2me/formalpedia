-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_shifted_two_sided_upcrossing_eq_original
-- name    : Kyprianou.Ch08.StageB.shifted_two_sided_upcrossing_eq_original
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T08:40:04.534246+00:00
-- url     : https://prove2.me/theorems/be8edb43-8b54-4fe3-97ce-0862ebc49735
-- title:
--   Exact shifted two-sided upcrossing discount integral equals original lower-negative upper-positive exit payoff
-- statement:
--   The up-before-down source discounted first-exit expectation for the spatially shifted process starting at l with upper barrier l+d equals the original process discounted strict upward first passage at d killed by strict downward first passage at negative l. This is an exact identity of the stopped clocks, including zero discount.
-- source:
--   Proof from the published definitions of shifted, tauPlus and tauMinus. Needed to apply the Proved Theorem 8.1 scale ratio and the Proved Kyprianou 8.2 no-drawdown upper bridge to genuine survival positivity.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.shifted_two_sided_upcrossing_eq_original
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (q l d : ℝ) :
    upBeforeDownExpectation P X q l (l + d) =
      ∫ ω, (if tauPlus X d ω < tauMinus X (-l) ω
        then discountedAt q (tauPlus X d ω) else 0) ∂P := by
  sorry
