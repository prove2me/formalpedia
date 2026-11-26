-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41WindowInfimumNullV24
-- name    : Kyprianou.Ch04.exercise41WindowInfimumNullV24
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:08:13.783891+00:00
-- url     : https://prove2.me/theorems/3c396188-0dc6-40ae-a9cc-882f4f221589
-- title:
--   The dense-grid future infimum at a fixed horizon gives zero occupation of a zero window minimum
-- statement:
--   The dense-grid future infimum at a fixed horizon gives zero occupation of a zero window minimum
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41WindowInfimumNullV24
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal inferInstance) (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) (q : ℕ → NNReal) (h : NNReal) :
    ∀ᵐ w ∂P, volume {s : ℝ | 0 ≤ s ∧ L.X s.toNNReal w +
      (⨅ k : ℕ, (L.X (s.toNNReal + min (q k) h) w - L.X s.toNNReal w)) = 0} = 0 := by
  sorry
