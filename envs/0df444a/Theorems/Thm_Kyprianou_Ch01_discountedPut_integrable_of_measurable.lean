-- Prove2me | Theorems.Thm_Kyprianou_Ch01_discountedPut_integrable_of_measurable
-- name    : Kyprianou.Ch01.discountedPut_integrable_of_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:02:30.813409+00:00
-- url     : https://prove2.me/theorems/53518f73-6b87-4fd9-ac04-06297509488d
-- title:
--   Integrability of measurable discounted perpetual-put payoffs
-- statement:
--   A measurable perpetual American put payoff evaluated at any possibly infinite stopping time is integrable under a probability law when the discount rate and strike are positive. The uniform pointwise bound by the strike supplies integrability.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.10, integrability component of the McKean perpetual put verification.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_discountedPut_pointwiseBound

open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.discountedPut_integrable_of_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (x K q : ℝ)
    (hK : 0 < K) (hq : 0 < q)
    (tau : Ω → WithTop ℝ≥0)
    (hMeas : Measurable (discountedPut X x K q tau)) :
    Integrable (discountedPut X x K q tau) P := by sorry
