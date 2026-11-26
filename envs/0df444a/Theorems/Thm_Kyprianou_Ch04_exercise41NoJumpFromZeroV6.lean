-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41NoJumpFromZeroV6
-- name    : Kyprianou.Ch04.exercise41NoJumpFromZeroV6
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:43:11.684668+00:00
-- url     : https://prove2.me/theorems/470d1a58-6e44-45a0-a42c-aebca0f864b6
-- title:
--   Almost surely no negative jump departs from a left-limit zero
-- statement:
--   Almost surely no negative jump departs from a left-limit zero
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41NoJumpFromZeroV6
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    ∀ᵐ w ∂P, ∀ s : NNReal, 0 < s →
      Function.leftLim (fun t => L.X t w) s = 0 → L.X s w = 0  := by
  sorry
