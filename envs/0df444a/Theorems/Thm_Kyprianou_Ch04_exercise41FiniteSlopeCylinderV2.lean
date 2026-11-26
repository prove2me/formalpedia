-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41FiniteSlopeCylinderV2
-- name    : Kyprianou.Ch04.exercise41FiniteSlopeCylinderV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:32:04.815782+00:00
-- url     : https://prove2.me/theorems/7b004dfa-5c66-56d4-9a30-b8af83960ec1
-- title:
--   Finite slope cylinder is measurable and contains full slope window
-- statement:
--   Finite slope cylinder is measurable and contains full slope window
-- source:
--   Kyprianou (2006), Chapter 4, Exercises 4.1 and 4.9.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41FiniteSlopeCylinderV2
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (δ : NNReal) (D : Finset NNReal)
    (hD : ∀ u ∈ D, 0 < u ∧ u ≤ δ) :
    let G : Set (NNReal → ℝ) :=
      {y | ∀ u ∈ D, L.drift / 2 * (u : ℝ) ≤ y u}
    MeasurableSet G ∧
      P {ω | ∀ u : NNReal, 0 < u → u ≤ δ →
          L.drift / 2 * (u : ℝ) ≤ L.X u ω} ≤
      P {ω | (fun u => L.X u ω) ∈ G}  := by
  sorry
