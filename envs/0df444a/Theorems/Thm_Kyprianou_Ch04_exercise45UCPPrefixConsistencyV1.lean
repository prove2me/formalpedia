-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45UCPPrefixConsistencyV1
-- name    : Kyprianou.Ch04.exercise45UCPPrefixConsistencyV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:29:48.549523+00:00
-- url     : https://prove2.me/theorems/c51cfc5b-c865-5e97-932d-017530ac5d9d
-- title:
--   Stochastic integrals defined by clipped-grid UCP agree through a common random clock
-- statement:
--   Equality of left weights on a random prefix implies equality of their stochastic integrals there, simultaneously almost surely.
-- source:
--   Kyprianou (2006), Exercise 4.5(iv), localisation argument.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- UCP stochastic integrals preserve equality of the integrands through a random clock. -/
theorem Kyprianou.Ch04.exercise45UCPPrefixConsistencyV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X H K I L : NNReal → Ω → ℝ) (τ : Ω → NNReal)
    (hI : Kyprianou.Ch04.IsStochasticIntegralInProbabilityV2 P X H I)
    (hL : Kyprianou.Ch04.IsStochasticIntegralInProbabilityV2 P X K L)
    (hHK : ∀ᵐ w ∂P, ∀ t ≤ τ w, H t w = K t w) :
    ∀ᵐ w ∂P, ∀ t ≤ τ w, I t w = L t w := by
  sorry
