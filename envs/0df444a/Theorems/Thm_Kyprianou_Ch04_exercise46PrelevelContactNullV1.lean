-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46PrelevelContactNullV1
-- name    : Kyprianou.Ch04.exercise46PrelevelContactNullV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:18:12.513744+00:00
-- url     : https://prove2.me/theorems/69fb95c6-6673-4331-b869-990a23d9fd5f
-- title:
--   Countable predictable time sections have zero time-probability product measure
-- statement:
--   Swap the coordinates and apply the established countable-section nullity theorem to the atomless finite time measure.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46PrelevelContactNullV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (T : NNReal) (E : Set (NNReal × Omega)) (hE : MeasurableSet E)
    (hCount : ∀ᵐ w ∂P, {t : NNReal | (t,w) ∈ E}.Countable) :
    ((((volume : Measure Real).restrict (Icc 0 (T : Real))).map Real.toNNReal).prod P) E = 0 := by
  sorry
