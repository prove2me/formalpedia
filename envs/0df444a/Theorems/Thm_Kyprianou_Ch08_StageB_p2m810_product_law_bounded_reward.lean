-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_product_law_bounded_reward
-- name    : Kyprianou.Ch08.StageB.p2m810_product_law_bounded_reward
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T21:58:02.077802+00:00
-- url     : https://prove2.me/theorems/04a76d30-1e3e-44e5-a89b-538811652c04
-- title:
--   A bounded jointly measurable payoff integrates through the joint product law, yielding the corresponding iterated conditional kernel integral.
-- statement:
--   A bounded jointly measurable payoff integrates through the joint product law, yielding the corresponding iterated conditional kernel integral.
-- source:
--   Kyprianou (2006), Exercise 8.10(iii)

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Instances.NNReal.Lemmas
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m810_product_law_bounded_reward
    {Ω β γ : Type} [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (Y : Ω → β) (V U : Ω → γ)
    (hY : Measurable Y) (hV : Measurable V) (hU : Measurable U)
    (hLaw : Measure.map (fun ω => (Y ω,V ω)) (P.restrict A) =
      (Measure.map Y (P.restrict A)).prod (Measure.map U P))
    (H : β × γ → ℝ) (hH : Measurable H) (C : ℝ)
    (hC : ∀ z, |H z| ≤ C) :
    (∫ ω in A, H (Y ω,V ω) ∂P) =
      ∫ ω in A, (∫ η, H (Y ω,U η) ∂P) ∂P := by
  sorry
