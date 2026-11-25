-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cadlagEndpointSupMeasurablePiProxy
-- name    : Kyprianou.Ch04.cadlagEndpointSupMeasurablePiProxy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:41:49.043778+00:00
-- url     : https://prove2.me/theorems/658439e8-ace0-46ac-9e40-9b95aa1485b1
-- title:
--   Measurable Pi-path proxy for a cadlag process's signed drawdown and supremum
-- statement:
--   Construct a measurable countable dyadic approximation to the endpoint and signed drawdown and take the pointwise limit on genuine right-continuous Levy paths, with an arbitrary measurable default elsewhere. Recover the supremum by adding the endpoint and positive drawdown.
-- source:
--   Kyprianou (2006), Exercise 4.8(ii–iii), p. 109; measurable transfer of Avram product-clock Wiener–Hopf law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.cadlagEndpointSupMeasurablePiProxy
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) :
    ∃ G : NNReal × (NNReal → ℝ) → ℝ × ℝ,
      Measurable G ∧ ∀ (t : NNReal) (ω : Ω),
        G (t, fun u : NNReal => L.X u ω) =
          (L.X t ω - runningSup L t ω, runningSup L t ω) := by
  sorry
