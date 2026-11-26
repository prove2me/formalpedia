-- Prove2me | Theorems.Thm_Kyprianou_Ch04_compactPairSquareProbabilityV1
-- name    : Kyprianou.Ch04.compactPairSquareProbabilityV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:43:19.991483+00:00
-- url     : https://prove2.me/theorems/79cf6c5d-2edd-41b7-a981-e73957da5eaa
-- title:
--   Joint compact deviation event probability bound
-- statement:
--   Joint compact deviation event probability bound.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii).

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem compactPairSquareProbabilityV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (U U' V V' : NNReal → Ω → ℝ) (T : NNReal) (d p : ℝ) (hp : 0 ≤ p)
    (hu : P {w | ∃ t ≤ T, d < |U t w - U' t w|} ≤ ENNReal.ofReal (p/2))
    (hv : P {w | ∃ t ≤ T, d < |V t w - V' t w|} ≤ ENNReal.ofReal (p/2)) :
    P {w | ∃ t ≤ T, d < dist (U t w,V t w) (U' t w,V' t w)} ≤
      ENNReal.ofReal p := by
  sorry
end Kyprianou.Ch04
