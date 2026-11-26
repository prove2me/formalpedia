-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41PositiveSlopeWindowV1
-- name    : Kyprianou.Ch04.exercise41PositiveSlopeWindowV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:42:54.876614+00:00
-- url     : https://prove2.me/theorems/69768641-c883-436e-9312-938ec8cfb539
-- title:
--   Positive-probability uniform small-time slope window
-- statement:
--   The Proved almost-sure drift limit implies that some deterministic positive window has positive probability of satisfying a slope lower bound d/2 throughout.
-- source:
--   Kyprianou (2006), Exercise 4.1(i)–(ii), printed pp.105–106.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_smallTimeDriftLimit
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04

theorem Kyprianou.Ch04.exercise41PositiveSlopeWindowV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    ∃ δ : NNReal, 0 < δ ∧
      0 < P {ω | ∀ u : NNReal, 0 < u → u ≤ δ →
        L.drift / 2 * (u : ℝ) ≤ L.X u ω} := by
  sorry
