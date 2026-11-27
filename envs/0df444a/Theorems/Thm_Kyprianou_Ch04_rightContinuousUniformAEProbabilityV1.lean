-- Prove2me | Theorems.Thm_Kyprianou_Ch04_rightContinuousUniformAEProbabilityV1
-- name    : Kyprianou.Ch04.rightContinuousUniformAEProbabilityV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T23:12:25.002084+00:00
-- url     : https://prove2.me/theorems/79ea7ef1-f6dd-50a1-a480-cf03abdc4111
-- title:
--   rightContinuousUniformAEProbabilityV1
-- statement:
--   rightContinuousUniformAEProbabilityV1
-- source:
--   Kyprianou (2006), Exercise 4.5(iii), measurable compact probability envelope

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_rightContinuousCompactEnvelopeV1
import Theorems.Thm_Kyprianou_Ch04_outerAEEventTailV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Almost-sure compact uniform convergence implies uniform outer convergence in probability. -/

theorem Kyprianou.Ch04.rightContinuousUniformAEProbabilityV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → NNReal → Ω → ℝ) (T : NNReal)
    (hM : ∀ n t, AEMeasurable (Y n t) P)
    (hR : ∀ n, ∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun s => Y n s w) (Ici t) t)
    (hC : ∀ᵐ w ∂P, ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, ∀ t ≤ T, |Y n t w| < δ)
    (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n => (P {w | ∃ t ≤ T, δ ≤ |Y n t w|}).toReal) atTop (nhds 0) := by
  sorry
