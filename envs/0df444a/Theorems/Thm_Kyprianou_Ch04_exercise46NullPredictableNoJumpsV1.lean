-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46NullPredictableNoJumpsV1
-- name    : Kyprianou.Ch04.exercise46NullPredictableNoJumpsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:18:13.720708+00:00
-- url     : https://prove2.me/theorems/1c44f282-a02f-4ae6-b7ab-65b8d49d652a
-- title:
--   A predictable time-probability null set contains no negative jumps almost surely
-- statement:
--   Compensation gives zero expected marked count. Identify the count pathwise with a measurable cardinality of negative jump times in E; its almost-sure vanishing excludes every such jump.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46NullPredictableNoJumpsV1
    {Omega : Type} [m : MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Filtration NNReal m) (L : SpectrallyNegativeLevy P G)
    (T : NNReal) (E : Set (NNReal × Omega))
    (hE : MeasurableSet[G.rightCont.predictable] E)
    (hAmb : MeasurableSet E) (hT : ∀ p ∈ E, p.1 ≤ T)
    (hNull : ((((volume : Measure Real).restrict (Icc 0 (T : Real))).map Real.toNNReal).prod P) E = 0) :
    ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t → (t,w) ∈ E →
      ¬ L.X t w < Function.leftLim (fun v : NNReal => L.X v w) t := by
  sorry
