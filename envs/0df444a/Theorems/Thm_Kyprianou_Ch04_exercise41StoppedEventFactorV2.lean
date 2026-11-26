-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41StoppedEventFactorV2
-- name    : Kyprianou.Ch04.exercise41StoppedEventFactorV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:33:32.344272+00:00
-- url     : https://prove2.me/theorems/8979c6e7-292a-56b3-a1fb-c2a1fa7cfbc3
-- title:
--   Stopped-event probability factors against the original Levy path law
-- statement:
--   Stopped-event probability factors against the original Levy path law
-- source:
--   Kyprianou (2006), Chapter 4, Exercises 4.1 and 4.9.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_restrictedFuturePath_mapLaw
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41StoppedEventFactorV2
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (τ : Ω → NNReal)
    (hτ : ∀ s, MeasurableSet[F s] {ω | τ ω ≤ s})
    (A : Set Ω)
    (hA : ∀ s, MeasurableSet[F s] (A ∩ {ω | τ ω ≤ s}))
    (G : Set (NNReal → ℝ)) (hG : MeasurableSet G) :
    P (A ∩ {ω | (fun u => L.X (τ ω + u) ω - L.X (τ ω) ω) ∈ G}) =
      P A * P {ω | (fun u => L.X u ω) ∈ G}  := by
  sorry
