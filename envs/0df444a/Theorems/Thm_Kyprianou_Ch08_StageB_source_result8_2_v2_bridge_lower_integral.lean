-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2_bridge_lower_integral
-- name    : Kyprianou.Ch08.StageB.source_result8_2_v2_bridge_lower_integral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T20:56:05.703033+00:00
-- url     : https://prove2.me/theorems/f5cc7081-775e-4f32-ae4e-624acfed7745
-- title:
--   Bridge 8.2 helper: no-drawdown integral bounded by up-before-down integral via AE inclusion
-- statement:
--   Given the AE inclusion of the no-drawdown event in the up-before-down event modulo infinite up-crossings (which carry zero discounted payoff), the no-drawdown set integral of the discounted clock is bounded by the full up-before-down integral. The integrands agree a.e. on the no-drawdown set, so their set integrals agree; the indicator-weighted integral is then bounded by the full integral. Strict-exit-clock aemeasurability plus accepted discountedAt bounds supply integrability. This discharges the integral-comparison core of lower slice 795c944f.
-- source:
--   Minimum source-faithful descendant of Kyprianou.Ch08.StageB.source_result8_2_v2_bridge_slice_lower [795c944f-7070-4a09-b77f-8e35067898de] (child of bridge efd9aabc-cb4e-4443-a2e5-0c09c61782a3). Takes the AE inclusion (proved from the tie-exclusion grandchild plus cadlag_ae and no_positive_jumps) as a hypothesis to avoid duplication; needs only q/D binders.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.source_result8_2_v2_bridge_lower_integral
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ l d : ℝ, 0 < l → 0 < d →
      (∀ᵐ ω ∂P, NoDrawdownBeforeUpcrossing D.X d l ω →
        tauPlus D.X d ω = ⊤ ∨ tauPlus D.X d ω < tauMinus D.X (-l) ω) →
      (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X d l ω}, discountedAt q (tauPlus D.X d ω) ∂P) ≤
        ∫ ω, (if tauPlus D.X d ω < tauMinus D.X (-l) ω then discountedAt q (tauPlus D.X d ω) else 0) ∂P := by
  sorry
