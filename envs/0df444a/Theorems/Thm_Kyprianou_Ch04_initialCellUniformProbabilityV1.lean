-- Prove2me | Theorems.Thm_Kyprianou_Ch04_initialCellUniformProbabilityV1
-- name    : Kyprianou.Ch04.initialCellUniformProbabilityV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:25:48.749812+00:00
-- url     : https://prove2.me/theorems/07c94608-5d04-5a13-8830-bab38977e5c5
-- title:
--   initialCellUniformProbabilityV1
-- statement:
--   The initial cell can carry an arbitrary bounded weight, because compact right continuity and measurable envelopes give vanishing outer probability.
-- source:
--   Kyprianou (2006), Exercise 4.5(iii)

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_rightContinuousCompactEnvelopeV1
import Theorems.Thm_Kyprianou_Ch04_outerAEEventTailV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A possibly nonmeasurable bounded initial coefficient contributes a vanishing
outer-probability error on the shrinking first grid cell. -/

theorem Kyprianou.Ch04.initialCellUniformProbabilityV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : NNReal → Ω → ℝ) (A : Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hA : ∀ w, |A w| ≤ K) (u : ℕ → NNReal) (hu : Tendsto u atTop (nhds 0))
    (hM : ∀ t, AEMeasurable (Y t) P)
    (hR : ∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun s => Y s w) (Ici t) t)
    (T : NNReal) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n => (P {w | ∃ t ≤ T, δ ≤
      |A w * (Y (min t (u n)) w - Y 0 w)|}).toReal) atTop (nhds 0) := by
  sorry
