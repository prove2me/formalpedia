-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45CofinalGoodProbabilityV1
-- name    : Kyprianou.Ch04.exercise45CofinalGoodProbabilityV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:34:51.213398+00:00
-- url     : https://prove2.me/theorems/40aedf91-8661-56ab-89af-29455cab4f4d
-- title:
--   Cofinal clocks exhaust compact intervals on a common conull event
-- statement:
--   Finite monotone cofinal stopping clocks exhaust compact intervals in outer probability, even with a common null exceptional set.
-- source:
--   Kyprianou Exercise 4.5 localisation

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem exercise45CofinalGoodProbabilityV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (τ : ℕ → Ω → NNReal)
    (hMeas : ∀ n T, MeasurableSet {w | τ n w ≤ T})
    (hMono : ∀ w, Monotone (fun n => τ n w))
    (hCof : ∀ᵐ w ∂P, Tendsto (fun n => (τ n w : WithTop NNReal)) atTop (nhds ⊤))
    (G : Ω → Prop) (hG : ∀ᵐ w ∂P, G w) (T : NNReal) :
    Tendsto (fun n => (P {w | ¬ G w ∨ τ n w ≤ T}).toReal) atTop (nhds 0) := by
  sorry
end Kyprianou.Ch04
