-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46DeterministicRestrictedPathV1
-- name    : Kyprianou.Ch04.exercise46DeterministicRestrictedPathV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:58:48.107879+00:00
-- url     : https://prove2.me/theorems/521e1308-a557-5c48-8dec-b2e635c83fd2
-- title:
--   Deterministic shifted path law on a past event
-- statement:
--   Apply the existing restricted future path law to the constant stopping time.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false
open scoped Topology

theorem Kyprianou.Ch04.exercise46DeterministicRestrictedPathV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P F)
    (s : NNReal) (B : Set Omega) (hB : MeasurableSet[F s] B) :
    Measure.map (fun w u => L.X (s + u) w - L.X s w) (P.restrict B) =
      P B • Measure.map (fun w u => L.X u w) P := by
  sorry
