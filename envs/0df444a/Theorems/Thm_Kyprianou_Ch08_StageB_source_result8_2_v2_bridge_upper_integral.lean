-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2_bridge_upper_integral
-- name    : Kyprianou.Ch08.StageB.source_result8_2_v2_bridge_upper_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T18:52:01.079803+00:00
-- url     : https://prove2.me/theorems/85412ab4-c37a-42de-9129-708443bb0b5e
-- title:
--   Bridge 8.2 helper: up-before-down integral bounded by no-drawdown integral
-- statement:
--   Given the pointwise inclusion of the unshifted up-before-down event in the no-drawdown event, the full integral of the up-before-down discounted payoff is bounded by the no-drawdown set integral. No measurability hypotheses: the full integral equals its no-drawdown set integral by forall-compl-eq-zero (off the no-drawdown set the up-before-down indicator vanishes), then set monotonicity for nonneg integrands against IntegrableOn of the discounted clock (8.1 strict-exit-clock aemeasurability plus accepted discountedAt bounds). This discharges the integral-comparison core of upper slice fe886010.
-- source:
--   Minimum source-faithful descendant of Kyprianou.Ch08.StageB.source_result8_2_v2_bridge_slice_upper [fe886010-e1c1-4101-92bd-c111ca85d838] (child of bridge efd9aabc-cb4e-4443-a2e5-0c09c61782a3). The corrected 84-line single-file upper proof (SHA 7f94dba5, sorry-free) was refused by complexity_risk 0.2360 vs cutoff -0.0523 (log 1795373473951310153-4); the measure-theoretic comparison block cannot fit with clocks, inclusion, and height-law isolation in one file. Takes the GC-A-derived inclusion as a hypothesis to avoid duplication; needs only q/D binders.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.source_result8_2_v2_bridge_upper_integral
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ l d : ℝ, 0 < l → 0 < d →
      ({ω | tauPlus D.X d ω < tauMinus D.X (-l) ω} ⊆
        {ω | NoDrawdownBeforeUpcrossing D.X d (l + d + d) ω}) →
      (∫ ω, (if tauPlus D.X d ω < tauMinus D.X (-l) ω then discountedAt q (tauPlus D.X d ω) else 0) ∂P) ≤
        ∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X d (l + d + d) ω},
          discountedAt q (tauPlus D.X d ω) ∂P := by
  sorry
