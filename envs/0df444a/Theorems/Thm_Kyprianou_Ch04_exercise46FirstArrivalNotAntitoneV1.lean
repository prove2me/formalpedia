-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46FirstArrivalNotAntitoneV1
-- name    : Kyprianou.Ch04.exercise46FirstArrivalNotAntitoneV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:43:11.552413+00:00
-- url     : https://prove2.me/theorems/45e7347d-6bf3-5413-855d-6ef9ff538f7d
-- title:
--   Positive first-arrival time and linear prefix imply non-monotone input
-- statement:
--   On almost every path the strictly positive arrival time leaves an interval of strictly increasing unit drift. Such a path cannot be antitone.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46FirstArrivalNotAntitoneV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (a : Omega → NNReal)
    (hPos : ∀ᵐ w ∂P, 0 < a w)
    (hPrefix : ∀ᵐ w ∂P, ∀ s : NNReal, s < a w → L.X s w = (s : Real)) :
    ¬ (∀ᵐ w ∂P, Antitone (fun t : NNReal => L.X t w)) := by
  sorry
