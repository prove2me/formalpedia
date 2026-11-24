-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_certain_record_ae
-- name    : Kyprianou.Ch08.StageB.p2m810_certain_record_ae
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T07:30:00.448015+00:00
-- url     : https://prove2.me/theorems/d8bbf14e-89e1-409b-8f1a-f6ec3b683f2f
-- title:
--   Unit record payoff implies strict record survival almost surely
-- statement:
--   The zero-discount payoff equals the indicator of the strict event. Expectation one under a probability measure implies the event holds almost surely. Integrability follows directly from nonzero integral.
-- source:
--   Kyprianou (2006), Theorem 8.10(i), zero right slope.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- Unit record payoff implies strict record survival almost surely -/
theorem p2m810_certain_record_ae :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (l a : ℝ),
      (∫ ω, if tauPlus X l ω < reflectedSupExit X 0 a ω
        then discountedAt 0 (tauPlus X l ω) else 0 ∂P) = 1 →
      ∀ᵐ ω ∂P, tauPlus X l ω < reflectedSupExit X 0 a ω := by
  sorry
end Kyprianou.Ch08.StageB
