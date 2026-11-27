-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45UCPIndistinguishableCongrV1
-- name    : Kyprianou.Ch04.exercise45UCPIndistinguishableCongrV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-27T00:10:47.624116+00:00
-- url     : https://prove2.me/theorems/43ff59b5-6e96-4986-acf1-1e7468302d2d
-- title:
--   Indistinguishable processes preserve clipped-grid UCP
-- statement:
--   The clipped-grid UCP definition is invariant under a simultaneous almost-sure modification of the integrand, integrator and integral.
-- source:
--   Kyprianou Exercise 4.5

import Mathlib
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
open MeasureTheory Filter Set Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A simultaneous almost-sure modification preserves clipped-grid UCP. -/
theorem Kyprianou.Ch04.exercise45UCPIndistinguishableCongrV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X H I Y K J : NNReal → Ω → ℝ)
    (hEq : ∀ᵐ w ∂P, ∀ t, X t w = Y t w ∧ H t w = K t w ∧ I t w = J t w)
    (hU : IsStochasticIntegralInProbabilityV2 P X H I) :
    IsStochasticIntegralInProbabilityV2 P Y K J := by
  sorry
